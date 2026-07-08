use ruff_python_ast as ast;
use smallvec::SmallVec;
use ty_module_resolver::Module;
use ty_python_core::definition::{Definition, DefinitionState};
use ty_python_core::place::PlaceExpr;
use ty_python_core::scope::ScopeId;
use ty_python_core::{
    BindingWithConstraintsIterator, BoundnessAnalysis, ProgramFile, global_scope, place_table,
    semantic_index, use_def_map,
};

use crate::place::{
    Place, builtins_module_scope, class_body_implicit_symbol, implicit_builtins_symbol,
    module_type_implicit_global_symbol,
};
use crate::place_load::{
    ImplicitPlaceLoad, PlaceLoadMode, PlaceLoadResolution, PlaceLoadResolutionStep,
    PlaceLoadSource, PlaceLoadSourceKind, resolve_place_load,
};
use crate::reachability::ReachabilityConstraintsExtension;
use crate::types::ProgramEnvironment;
use crate::{Db, SemanticModel};

use super::user_visible_definitions;

impl<'db> SemanticModel<'db> {
    /// Resolves the possible value providers for a name load.
    ///
    /// Returns `None` when choosing the correct binding state would require type inference.
    pub fn name_load(&self, name: &ast::ExprName) -> Option<NameLoadResolution<'db>> {
        let file_scope = self.scope(name.into())?;
        let index = semantic_index(self.db(), self.program_file());
        let scope = file_scope.to_scope_id(self.db(), self.program_file());
        let mode = if self.is_in_string_annotation() {
            PlaceLoadMode::StringAnnotation
        } else if index.place_load_is_deferred(ast::ExprRef::Name(name))? {
            PlaceLoadMode::Deferred
        } else {
            PlaceLoadMode::AtExpression(name.into())
        };
        let environment = self.program_environment();
        let resolution = resolve_place_load(
            self.db(),
            index,
            scope,
            PlaceExpr::from_expr_name(name),
            mode,
        );

        Some(NameLoadResolution::from_place_load(
            self.db(),
            &environment,
            scope,
            resolution,
        ))
    }

    /// Returns the possible providers for an explicit module global.
    pub fn module_global_providers(
        &self,
        module: Module<'db>,
        name: &str,
    ) -> Option<ValueProviders<'db>> {
        let file = module.file(self.db())?;
        let file = ProgramFile::new(self.db(), file, self.program());
        let scope = global_scope(self.db(), file);
        let symbol = place_table(self.db(), scope).symbol_id(name)?;
        Some(ValueProviders::from_bindings(
            self.db(),
            use_def_map(self.db(), scope).end_of_scope_symbol_bindings(symbol),
        ))
    }
}

/// The value providers for a name load.
pub struct NameLoadResolution<'db> {
    providers: ValueProviders<'db>,
    crosses_scope_declaration: bool,
}

impl<'db> NameLoadResolution<'db> {
    /// Returns the possible value providers.
    pub fn providers(&self) -> &ValueProviders<'db> {
        &self.providers
    }

    /// Returns whether resolution crosses a `global` or `nonlocal` declaration.
    pub fn crosses_scope_declaration(&self) -> bool {
        self.crosses_scope_declaration
    }

    fn from_place_load(
        db: &'db dyn Db,
        environment: &ProgramEnvironment<'db>,
        scope: ScopeId<'db>,
        mut resolution: PlaceLoadResolution<'db, '_>,
    ) -> Self {
        let mut providers = ValueProviders::default();
        let mut may_be_unbound = true;

        while may_be_unbound {
            let Some(step) = resolution.next() else {
                break;
            };
            match step {
                PlaceLoadResolutionStep::Source(source) => {
                    let mut source_providers =
                        value_providers_for_source(db, environment, scope, &source);
                    if source.is_class_body_global_fallback() && source_providers.has_provider() {
                        source_providers.may_be_unbound = false;
                    }
                    may_be_unbound = source_providers.may_be_unbound;
                    providers.extend(source_providers);
                }
                PlaceLoadResolutionStep::MemberResolutionCondition(_) => {
                    providers.has_unrepresented_provider = true;
                    break;
                }
                PlaceLoadResolutionStep::Exhausted(_) => break,
            }
        }

        providers.may_be_unbound = may_be_unbound;
        Self {
            providers,
            crosses_scope_declaration: resolution.crosses_scope_declaration(),
        }
    }
}

/// The definitions that may provide a value.
pub struct ValueProviders<'db> {
    definitions: SmallVec<[Definition<'db>; 2]>,
    has_unrepresented_provider: bool,
    may_be_unbound: bool,
    may_be_deleted: bool,
}

impl<'db> ValueProviders<'db> {
    /// Returns the source definitions that may provide the value.
    pub fn definitions(&self) -> impl ExactSizeIterator<Item = Definition<'db>> + '_ {
        self.definitions.iter().copied()
    }

    /// Returns whether a possible provider has no source definition.
    pub fn has_unrepresented_provider(&self) -> bool {
        self.has_unrepresented_provider
    }

    /// Returns whether every feasible path provides a value.
    pub fn is_definitely_bound(&self) -> bool {
        !self.may_be_unbound
    }

    /// Returns whether a reachable deletion may leave the value unbound.
    pub fn may_be_deleted(&self) -> bool {
        self.may_be_deleted
    }

    fn from_bindings(
        db: &'db dyn Db,
        mut bindings: BindingWithConstraintsIterator<'db, 'db>,
    ) -> Self {
        let boundness = bindings.boundness_analysis();
        let mut providers = Self::default();

        while let Some(binding) = bindings.next() {
            let reachability = bindings.reachability_constraints().evaluate(
                db,
                bindings.predicates(),
                binding.reachability_constraint,
            );
            if reachability.is_always_false() {
                continue;
            }

            match binding.binding {
                DefinitionState::Defined(definition) => providers.push_definition(db, definition),
                DefinitionState::Deleted => {
                    let may_be_deleted = reachability.may_be_true();
                    providers.may_be_unbound |= may_be_deleted;
                    providers.may_be_deleted |= may_be_deleted;
                }
                DefinitionState::Undefined
                    if boundness == BoundnessAnalysis::BasedOnUnboundVisibility =>
                {
                    providers.may_be_unbound |= reachability.may_be_true();
                }
                DefinitionState::Undefined => {}
            }
        }

        if !providers.has_provider() {
            providers.may_be_unbound = true;
        }
        providers
    }

    fn push_definition(&mut self, db: &'db dyn Db, definition: Definition<'db>) {
        let definitions = user_visible_definitions(db, [definition]);
        if definitions.is_empty() {
            self.has_unrepresented_provider = true;
            return;
        }
        for definition in definitions {
            if !self.definitions.contains(&definition) {
                self.definitions.push(definition);
            }
        }
    }

    fn from_unrepresented(place: Place<'db>) -> Self {
        Self {
            has_unrepresented_provider: !place.is_undefined(),
            may_be_unbound: !place.is_definitely_bound(),
            ..Self::default()
        }
    }

    fn has_provider(&self) -> bool {
        self.has_unrepresented_provider || !self.definitions.is_empty()
    }

    fn extend(&mut self, other: Self) {
        for definition in other.definitions {
            if !self.definitions.contains(&definition) {
                self.definitions.push(definition);
            }
        }
        self.has_unrepresented_provider |= other.has_unrepresented_provider;
        self.may_be_deleted |= other.may_be_deleted;
    }
}

impl Default for ValueProviders<'_> {
    fn default() -> Self {
        Self {
            definitions: SmallVec::new(),
            has_unrepresented_provider: false,
            may_be_unbound: false,
            may_be_deleted: false,
        }
    }
}

fn value_providers_for_source<'db>(
    db: &'db dyn Db,
    environment: &ProgramEnvironment<'db>,
    scope: ScopeId<'db>,
    source: &PlaceLoadSource<'db>,
) -> ValueProviders<'db> {
    match &source.kind {
        PlaceLoadSourceKind::Bindings(bindings) => {
            ValueProviders::from_bindings(db, bindings.clone())
        }
        PlaceLoadSourceKind::DefinitionsFromOwningScope { scope, id } => {
            ValueProviders::from_bindings(db, use_def_map(db, *scope).reachable_bindings(*id))
        }
        PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ExplicitGlobalSymbol { file, name }) => {
            let scope = global_scope(db, *file);
            let Some(symbol) = place_table(db, scope).symbol_id(name) else {
                return ValueProviders {
                    may_be_unbound: true,
                    ..ValueProviders::default()
                };
            };
            ValueProviders::from_bindings(
                db,
                use_def_map(db, scope).reachable_symbol_bindings(symbol),
            )
        }
        PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::DunderClass(definition)) => {
            let mut providers = ValueProviders::default();
            providers.push_definition(db, *definition);
            providers
        }
        PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ClassBodySymbol(name)) => {
            ValueProviders::from_unrepresented(
                class_body_implicit_symbol(db, environment, name).place,
            )
        }
        PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::ModuleImplicitGlobal { file, name }) => {
            ValueProviders::from_unrepresented(
                module_type_implicit_global_symbol(db, *file, name).place,
            )
        }
        PlaceLoadSourceKind::Implicit(ImplicitPlaceLoad::Builtin(name)) => {
            let place = if Some(scope) == builtins_module_scope(db, environment) {
                Place::Undefined
            } else {
                implicit_builtins_symbol(db, environment, name).place
            };
            ValueProviders::from_unrepresented(place)
        }
    }
}

#[cfg(test)]
mod tests {
    use ruff_db::files::system_path_to_file;
    use ruff_db::parsed::parsed_module;
    use ruff_python_ast::visitor::{Visitor, walk_expr};
    use ruff_python_ast::{self as ast, PythonVersion};
    use ruff_text_size::Ranged;
    use ty_python_core::ProgramFile;

    use crate::SemanticModel;
    use crate::db::tests::TestDbBuilder;

    #[test]
    fn name_load_uses_point_in_time_bindings() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.py",
                "import first as value\nbefore = value\nimport second as value\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let use_name = ast.suite()[1]
            .as_assign_stmt()
            .unwrap()
            .value
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();
        let definitions = load.providers().definitions().collect::<Vec<_>>();

        assert_eq!(definitions.len(), 1);
        Ok(())
    }

    #[test]
    fn name_load_uses_end_of_scope_bindings_for_deferred_annotations() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.pyi",
                "import first as value\nbefore: value.C\nimport second as value\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.pyi").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let use_name = ast.suite()[1]
            .as_ann_assign_stmt()
            .unwrap()
            .annotation
            .as_attribute_expr()
            .unwrap()
            .value
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();
        let definitions = load.providers().definitions().collect::<Vec<_>>();

        assert_eq!(definitions.len(), 2);
        Ok(())
    }

    #[test]
    fn name_load_uses_end_of_scope_bindings_with_future_annotations() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_python_version(PythonVersion::PY313)
            .with_file(
                "/src/foo.py",
                "from __future__ import annotations\nimport first as value\nbefore: value.C\nimport second as value\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let use_name = ast.suite()[2]
            .as_ann_assign_stmt()
            .unwrap()
            .annotation
            .as_attribute_expr()
            .unwrap()
            .value
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();

        assert_eq!(load.providers().definitions().count(), 2);
        Ok(())
    }

    #[test]
    fn name_load_uses_end_of_scope_bindings_for_python_314_annotations() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_python_version(PythonVersion::PY314)
            .with_file(
                "/src/foo.py",
                "import first as value\nbefore: value.C\nimport second as value\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let use_name = ast.suite()[1]
            .as_ann_assign_stmt()
            .unwrap()
            .annotation
            .as_attribute_expr()
            .unwrap()
            .value
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();

        assert_eq!(load.providers().definitions().count(), 2);
        Ok(())
    }

    #[test]
    fn name_load_returns_none_when_deferredness_requires_inference() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file("/src/foo.pyi", "import first as value\nbefore = value\n")
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.pyi").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let use_name = ast.suite()[1]
            .as_assign_stmt()
            .unwrap()
            .value
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);

        assert!(model.name_load(use_name).is_none());
        Ok(())
    }

    #[test]
    fn name_load_uses_end_of_scope_bindings_in_other_deferred_contexts() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.pyi",
                "import first as value\ndef function[T: value.C](arg=value): ...\nclass Class(value.C): ...\ntype Alias = value.C\ncallback = lambda arg=value: None\nimport second as value\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.pyi").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let model = SemanticModel::new(&db, file);
        let uses = loaded_names(ast.syntax(), "value");

        assert_eq!(uses.len(), 5);
        for name in uses {
            let load = model.name_load(name).unwrap();
            assert_eq!(load.providers().definitions().count(), 2);
        }
        Ok(())
    }

    #[test]
    fn name_load_excludes_bindings_that_do_not_reach_the_use() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.py",
                "def test(flag: bool):\n    if flag:\n        x: int = 1\n        return\n    x = 2\n    print(x)\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = ast.suite()[0].as_function_def_stmt().unwrap();
        let assignment = function.body[1].as_assign_stmt().unwrap();
        let use_name = function.body[2]
            .as_expr_stmt()
            .unwrap()
            .value
            .as_call_expr()
            .unwrap()
            .arguments
            .args[0]
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();
        let definitions = load.providers().definitions().collect::<Vec<_>>();

        assert_eq!(definitions.len(), 1);
        assert_eq!(
            definitions[0].focus_range(&db, &ast).range(),
            assignment.targets[0].range()
        );
        Ok(())
    }

    #[test]
    fn name_load_respects_redeclarations() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.py",
                "def test(flag: bool):\n    if flag:\n        x: int = 10\n    else:\n        x: str = 'test'\n    print(x)\n    x: int = 30\n    print(x)\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = ast.suite()[0].as_function_def_stmt().unwrap();
        let first_use = function.body[1]
            .as_expr_stmt()
            .unwrap()
            .value
            .as_call_expr()
            .unwrap()
            .arguments
            .args[0]
            .as_name_expr()
            .unwrap();
        let redeclaration = function.body[2].as_ann_assign_stmt().unwrap();
        let second_use = function.body[3]
            .as_expr_stmt()
            .unwrap()
            .value
            .as_call_expr()
            .unwrap()
            .arguments
            .args[0]
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let first_definitions = model
            .name_load(first_use)
            .unwrap()
            .providers()
            .definitions()
            .collect::<Vec<_>>();
        let second_definitions = model
            .name_load(second_use)
            .unwrap()
            .providers()
            .definitions()
            .collect::<Vec<_>>();

        assert_eq!(first_definitions.len(), 2);
        assert!(
            first_definitions.iter().all(|definition| {
                definition.focus_range(&db, &ast).start() < first_use.start()
            })
        );
        assert_eq!(second_definitions.len(), 1);
        assert_eq!(
            second_definitions[0].focus_range(&db, &ast).range(),
            redeclaration.target.range()
        );
        Ok(())
    }

    #[test]
    fn name_load_reports_possible_unboundness() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.py",
                "def test(flag: bool):\n    if flag:\n        import other as value\n    return value\n",
            )
            .with_file("/src/other.py", "")
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = ast.suite()[0].as_function_def_stmt().unwrap();
        let use_name = function.body[1]
            .as_return_stmt()
            .unwrap()
            .value
            .as_ref()
            .unwrap()
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();

        assert_eq!(load.providers().definitions().count(), 1);
        assert!(!load.providers().is_definitely_bound());
        assert!(!load.providers().may_be_deleted());
        Ok(())
    }

    #[test]
    fn name_load_reports_reachable_deletions() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.py",
                "def test(flag: bool):\n    import other as value\n    if flag:\n        del value\n    return value\n",
            )
            .with_file("/src/other.py", "")
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = ast.suite()[0].as_function_def_stmt().unwrap();
        let use_name = function.body[2]
            .as_return_stmt()
            .unwrap()
            .value
            .as_ref()
            .unwrap()
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();

        assert_eq!(load.providers().definitions().count(), 1);
        assert!(!load.providers().is_definitely_bound());
        assert!(load.providers().may_be_deleted());
        Ok(())
    }

    #[test]
    fn name_load_distinguishes_implicit_providers_from_missing_names() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file("/src/foo.py", "def test():\n    return int, missing_name\n")
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = ast.suite()[0].as_function_def_stmt().unwrap();
        let tuple = function.body[0]
            .as_return_stmt()
            .unwrap()
            .value
            .as_ref()
            .unwrap()
            .as_tuple_expr()
            .unwrap();
        let builtin = tuple.elts[0].as_name_expr().unwrap();
        let missing = tuple.elts[1].as_name_expr().unwrap();
        let model = SemanticModel::new(&db, file);
        let builtin = model.name_load(builtin).unwrap();
        let missing = model.name_load(missing).unwrap();

        assert!(builtin.providers().has_unrepresented_provider());
        assert!(builtin.providers().is_definitely_bound());
        assert!(!missing.providers().has_unrepresented_provider());
        assert!(!missing.providers().is_definitely_bound());
        Ok(())
    }

    #[test]
    fn name_load_reports_scope_declarations() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/foo.py",
                "value = 1\ndef test():\n    global value\n    return value\n",
            )
            .build()?;
        let file = system_path_to_file(&db, "/src/foo.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let ast = parsed_module(&db, file.python_file(&db)).load(&db);
        let function = ast.suite()[1].as_function_def_stmt().unwrap();
        let use_name = function.body[1]
            .as_return_stmt()
            .unwrap()
            .value
            .as_ref()
            .unwrap()
            .as_name_expr()
            .unwrap();
        let model = SemanticModel::new(&db, file);
        let load = model.name_load(use_name).unwrap();

        assert_eq!(load.providers().definitions().count(), 1);
        assert!(load.crosses_scope_declaration());
        Ok(())
    }

    #[test]
    fn module_global_providers_use_end_of_scope_bindings() -> anyhow::Result<()> {
        let db = TestDbBuilder::new()
            .with_file(
                "/src/pkg/__init__.py",
                "if flag:\n    from . import first as value\nelse:\n    from . import second as value\n",
            )
            .with_file("/src/pkg/first.py", "")
            .with_file("/src/pkg/second.py", "")
            .with_file("/src/use.py", "import pkg\n")
            .build()?;
        let file = system_path_to_file(&db, "/src/use.py").unwrap();
        let file = ProgramFile::new(&db, file, db.program_environment().program(&db));
        let model = SemanticModel::new(&db, file);
        let module = model.resolve_module(Some("pkg"), 0).unwrap();
        let providers = model.module_global_providers(module, "value").unwrap();

        assert_eq!(providers.definitions().count(), 2);
        assert!(providers.is_definitely_bound());
        Ok(())
    }

    fn loaded_names<'ast>(
        module: &'ast ast::ModModule,
        searched: &str,
    ) -> Vec<&'ast ast::ExprName> {
        struct Collector<'ast, 'name> {
            searched: &'name str,
            names: Vec<&'ast ast::ExprName>,
        }

        impl<'ast> Visitor<'ast> for Collector<'ast, '_> {
            fn visit_expr(&mut self, expression: &'ast ast::Expr) {
                if let ast::Expr::Name(name) = expression
                    && name.ctx.is_load()
                    && name.id == self.searched
                {
                    self.names.push(name);
                }
                walk_expr(self, expression);
            }
        }

        let mut collector = Collector {
            searched,
            names: Vec::new(),
        };
        collector.visit_body(&module.body);
        collector.names
    }
}
