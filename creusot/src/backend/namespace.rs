//! Handles generation of the namespace type.

use super::Why3Generator;
use why3::{declaration::Decl, ty::Type};

impl Why3Generator<'_> {
    /// Get the declarations for `type namespace = ...`
    pub(super) fn generate_namespace_type(&self, namespace_ty: why3::Name) -> Vec<Decl> {
        let namespace_other_name = why3::Ident::fresh_local("namespace_other");
        let other_namespaces_type = why3::declaration::TyDecl::Opaque {
            ty_name: namespace_other_name,
            ty_params: [].into(),
        };

        let namespaces = self.namespaces.borrow();
        let namespaces = why3::declaration::TyDecl::Adt {
            tys: [why3::declaration::AdtDecl {
                ty_name: namespace_ty.to_ident(),
                ty_params: [].into(),
                sumrecord: why3::declaration::SumRecord::Sum(
                    namespaces
                        .values()
                        .map(|n| why3::declaration::ConstructorDecl {
                            name: *n,
                            fields: [Type::qconstructor(why3::QName::parse("int"))].into(),
                        })
                        .chain(std::iter::once(why3::declaration::ConstructorDecl {
                            name: why3::Ident::fresh_local("Other"),
                            fields: [Type::TConstructor(why3::Name::local(namespace_other_name))]
                                .into(),
                        }))
                        .collect(),
                ),
            }]
            .into(),
        };
        vec![
            why3::declaration::Decl::TyDecl(other_namespaces_type.clone()),
            why3::declaration::Decl::TyDecl(namespaces.clone()),
        ]
    }
}
