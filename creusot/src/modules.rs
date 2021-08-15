use why3::declaration::{Decl, Module, Predicate, TyDecl, Use};
use why3::mlcfg::QName;

#[derive(Debug)]
pub struct Modules {
    types: Vec<(TyDecl, Predicate)>,
    mods: Vec<Module>,
}

impl Modules {
    pub fn new() -> Self {
        Self { types: Vec::new(), mods: Vec::new() }
    }

    pub fn add_module(&mut self, mdl: Module) {
        self.mods.push(mdl)
    }

    pub fn add_type(&mut self, decl: TyDecl, drop: Predicate) {
        let mut dependencies = decl.used_types();
        let mut pos = 0;
        while !dependencies.is_empty() && pos < self.types.len() {
            dependencies.remove(&self.types[pos].0.ty_name);
            pos += 1;
        }

        self.types.insert(pos, (decl, drop));
    }

    pub fn into_iter(self) -> impl Iterator<Item = Decl> {
        std::iter::once(Decl::Module(Module {
            name: "Type".into(),
            decls: vec![
                Decl::UseDecl(Use { name: QName::from_string("Ref").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.Int").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.Int32").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.Int64").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt32").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt64").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("string.Char").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("floating_point.Single").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("floating_point.Double").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("prelude.Prelude").unwrap() }),
            ]
            .into_iter()
            .chain(self.types.into_iter().flat_map(|(ty, p)| [Decl::TyDecl(ty), Decl::PredDecl(p)]))
            .collect(),
        }))
        .chain(self.mods.into_iter().map(|mut md| {
            md.decls = vec![
                Decl::UseDecl(Use { name: QName::from_string("Ref").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.Int").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.Int32").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.Int64").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt32").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt64").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("string.Char").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("floating_point.Single").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("floating_point.Double").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("prelude.Prelude").unwrap() }),
                Decl::UseDecl(Use { name: QName::from_string("Type").unwrap() }),
            ]
            .into_iter()
            .chain(md.decls.into_iter())
            .collect();
            Decl::Module(md)
        }))
    }
}
