use crate::term::*;
use std::collections::HashMap;

pub trait GlobalContext {
    fn resolve_name(&self, path: &Name) -> Option<Type>;
    fn constructor_type(&self, path: &Name) -> Option<(Vec<Type>, Type)>;
}

type LocalIdent = String;

pub struct TypeContext<G: GlobalContext> {
    global_ctx: G,
    local_ctx: Vec<HashMap<LocalIdent, Type>>,
    // substitution: UnifSubst,
    unif: InPlaceUnificationTable<TyUnk>,
}

impl<G: GlobalContext> TypeContext<G> {
    pub fn new(glbl: G) -> Self {
        Self::new_with_ctx(glbl, HashMap::new())
    }

    pub fn new_with_ctx<C>(glbl: G, ctx: C) -> Self
    where
        C: IntoIterator<Item = (LocalIdent, Type)>,
    {
        TypeContext {
            global_ctx: glbl,
            local_ctx: vec![ctx.into_iter().collect()],
            unif: InPlaceUnificationTable::new(),
        }
    }
}

// impl<G: GlobalContext> GlobalContext for TypeContext<G> {

// }

impl<G: GlobalContext> TypeContext<G> {
    fn resolve_name(&mut self, path: &Name) -> Option<Type> {
        if let Name::Ident(ident) = path {
            for scope in self.local_ctx.iter().rev() {
                if let Some(ty) = scope.get(ident) {
                    return Some(ty.clone());
                }
            }
            // TODO: UNHACK this
            self.global_ctx.resolve_name(path).map(|mut ty| {
                self.freshen(&mut ty);
                ty
            })
        } else {
            // TODO: UNHACK this
            self.global_ctx.resolve_name(path).map(|mut ty| {
                self.freshen(&mut ty);
                ty
            })
        }
    }

    // fn constructor_type(&self, path: &Name) -> Option<(Vec<Type>, Type)> {
    //     self.global_ctx.constructor_type(path)
    // }

    fn register_var(&mut self, path: &Ident, ty: Type) {
        self.local_ctx.last_mut().unwrap().insert(path.0.clone(), ty);
    }

    // TODO move it out of this trait
    fn fresh_ty(&mut self) -> Type {
        Type::Unknown(self.unif.new_key(None))
    }

    fn freshen(&mut self, ty: &mut Type) {
        use Type::*;
        match ty {
            Reference { kind: _, ty } => self.freshen(ty),
            Tuple { elems } => elems.iter_mut().for_each(|t| self.freshen(t)),
            Function { args, res } => {
                args.iter_mut().for_each(|arg| self.freshen(arg));
                self.freshen(res);
            }
            App { func, args } => {
                self.freshen(func);
                args.iter_mut().for_each(|arg| self.freshen(arg));
            }
            Var(_) => *ty = self.fresh_ty(),
            Path { .. } | Lit(_) | Unknown(_) => {}
        }
    }
    // Substitute in all solved variables
    pub fn zonk(&mut self, ty: &mut Type) {
        use Type::*;
        match ty {
            Reference { kind: _, ty } => self.zonk(ty),
            Tuple { elems } => elems.iter_mut().for_each(|t| self.zonk(t)),
            Unknown(uk) => {
                if let Some(t) = self.unif.probe_value(*uk) {
                    *ty = t;
                    self.zonk(ty);
                } else {
                    *ty = Type::Var(uk.zonk());
                }
            }
            App { func, args } => {
                self.zonk(func);
                args.iter_mut().for_each(|arg| self.zonk(arg));
            }
            Function { args, res } => {
                args.iter_mut().for_each(|arg| self.zonk(arg));
                self.zonk(res);
            }
            _ => {}
        }
    }

    fn fresh_cons_type(&mut self, path: &Name) -> Option<(Vec<Type>, Type)> {
        let (mut field_tys, mut ret_ty) = self.global_ctx.constructor_type(path)?;
        let var_subst: VarSubst =
            ret_ty.fvs().into_iter().map(|fv| (fv, self.fresh_ty())).collect();

        field_tys.iter_mut().for_each(|fld| var_subst.subst(fld));
        var_subst.subst(&mut ret_ty);

        Some((field_tys, ret_ty))
    }

    fn scope<F, R>(&mut self, scope: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
        Self: Sized,
    {
        self.local_ctx.push(Default::default());
        let ret = scope(self);
        self.local_ctx.pop();
        ret
    }

    fn unify(&mut self, expected: &Type, inferred: &Type) -> Result<(), TypeError> {
        use Type::*;
        match (expected, inferred) {
            (Unknown(uk), a) | (a, Unknown(uk)) => {
                match self.unif.unify_var_value(*uk, Some(a.clone())) {
                    Err((l, r)) => self.unify(&l, &r),
                    Ok(()) => Ok(()),
                }
            }
            (Tuple { elems: a }, Tuple { elems: b }) => {
                for (t1, t2) in a.iter().zip(b.iter()) {
                    self.unify(&t1, &t2)?;
                }
                Ok(())
            }
            (Reference { kind: k1, ty: box t1 }, Reference { kind: k2, ty: box t2 })
                if k1 == k2 =>
            {
                self.unify(t1, t2)
            }
            (App { func: f1, args: a1 }, App { func: f2, args: a2 }) => {
                self.unify(f1, f2)?;
                for (a1, a2) in a1.iter().zip(a2.iter()) {
                    self.unify(a1, a2)?;
                }
                Ok(())
            }
            (a, b) => {
                if a == b {
                    Ok(())
                } else {
                    let mut a = a.clone();
                    let mut b = b.clone();
                    self.zonk(&mut a);
                    self.zonk(&mut b);
                    Err(UnificationError(a, b))
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    GenericError,
    InvalidCast(Type, Type),
    UnificationError(Type, Type),
    UnknownVariable(Name),
    UnknownConstructor(Name),
    NotFunction(Type, Name),
}

use ena::unify::InPlaceUnificationTable;
use TypeError::*;

pub fn infer_term<G>(ctx: &mut TypeContext<G>, term: &mut Term) -> Result<Type, TypeError>
where
    G: GlobalContext,
{
    use Term::*;
    match term {
        Match { expr, arms } => {
            let scrut_ty = infer_term(ctx, expr)?;
            let body_ty = ctx.fresh_ty();

            for MatchArm { pat, box body } in arms {
                ctx.scope(|ctx| {
                    check_pattern(ctx, pat, &scrut_ty)?;
                    check_term(ctx, body, &body_ty)?;
                    Ok(())
                })?;
            }
            Ok(body_ty)
        }
        If { box cond, box then_branch, box else_branch } => {
            check_term(ctx, cond, &Type::Lit(LitTy::Boolean))?;

            let ty = infer_term(ctx, then_branch)?;
            check_term(ctx, else_branch, &ty)?;

            Ok(ty)
        }
        Binary { left, op, right } => {
            let left_ty = infer_term(ctx, left)?;
            let right_ty = infer_term(ctx, right)?;
            let res_ty = binop_type(ctx, &op, &left_ty, &right_ty)?;

            Ok(res_ty)
        }
        Lit { lit } => Ok(Type::Lit(typecheck_lit(lit))),
        Variable { path } => ctx.resolve_name(path).ok_or_else(||UnknownVariable(path.clone())),
        Tuple { elems } => {
            let elem_tys =
                elems.iter_mut().map(|e| infer_term(ctx, e)).collect::<Result<Vec<_>, _>>()?;
            Ok(Type::Tuple { elems: elem_tys })
        }
        Call { func, args } => {
            let fty = ctx.resolve_name(func).ok_or_else(||UnknownVariable(func.clone()))?;
            // TODO: This is wrong in if we have lambdas
            // ctx.freshen(&mut fty);
            // ctx.zonk(&mut fty);

            if let Type::Function { args: arg_tys, box res } = fty {
                for (arg, ty) in args.iter_mut().zip(arg_tys.iter()) {
                    check_term(ctx, arg, ty)?;
                }
                Ok(res)
            } else {
                Err(NotFunction(fty, func.clone()))
            }
        }
        Let { pat, box arg, box body } => {
            let ty = infer_term(ctx, arg)?;

            ctx.scope(|ctx| {
                check_pattern(ctx, pat, &ty)?;
                infer_term(ctx, body)
            })
        }
        Exists { args, box body } | Forall { args, box body } => ctx.scope(|ctx| {
            args.iter().for_each(|(id, ty)| {
                ctx.register_var(id, ty.clone());
            });

            check_term(ctx, body, &Type::Lit(LitTy::Boolean))?;
            Ok(Type::Lit(LitTy::Boolean))
        }),
        Unary { op: UnOp::Final, box expr } | Unary { op: UnOp::Current, box expr } => {
            let inner = ctx.fresh_ty();
            let refty = Type::Reference { kind: RefKind::Mut, ty: box inner.clone() };
            check_term(ctx, expr, &refty)?;
            Ok(inner)
        }
        Unary { op: UnOp::Not, box expr } => {
            check_term(ctx, expr, &Type::Lit(LitTy::Boolean))?;
            Ok(Type::Lit(LitTy::Boolean))
        }
        Unary { op: UnOp::Neg, expr: _ } => {
            unimplemented!("negation");
        }
        Cast { expr, ty } => {
            let mut inner_ty = infer_term(ctx, expr)?;
            ctx.zonk(&mut inner_ty);

            if !ty.is_numeric() && inner_ty.is_numeric() {
                Err(InvalidCast(inner_ty, ty.clone()))
            } else {
                Ok(ty.clone())
            }
        }
        Absurd => Ok(ctx.fresh_ty()),
    }
}

pub fn check_term<G>(
    ctx: &mut TypeContext<G>,
    term: &mut Term,
    expected: &Type,
) -> Result<(), TypeError>
where
    G: GlobalContext,
{
    let inferred = infer_term(ctx, term)?;
    ctx.unify(expected, &inferred)?;
    Ok(())
}

fn check_pattern<G>(
    ctx: &mut TypeContext<G>,
    pat: &mut Pattern,
    expected: &Type,
) -> Result<(), TypeError>
where
    G: GlobalContext,
{
    use Pattern::*;
    match pat {
        Var(x) => {
            ctx.register_var(x, expected.clone());
            Ok(())
        }
        Struct { path, fields } => {
            let (field_tys, ret_ty) = ctx.fresh_cons_type(path).ok_or(GenericError)?;

            ctx.unify(&ret_ty, expected)?;

            for ((_, pat), ty) in fields.iter_mut().zip(field_tys.iter()) {
                check_pattern(ctx, pat, ty)?;
            }
            Ok(())
        }
        TupleStruct { path, fields } => {
            let (field_tys, ret_ty) =
                ctx.fresh_cons_type(path).ok_or_else(||UnknownConstructor(path.clone()))?;
            ctx.unify(&ret_ty, expected)?;

            for (pat, ty) in fields.iter_mut().zip(field_tys.iter()) {
                check_pattern(ctx, pat, ty)?;
            }
            Ok(())
        }
        Boolean(_) => ctx.unify(&Type::BOOLEAN, expected),
        Wild => Ok(()),
    }
}

fn binop_type<G: GlobalContext>(
    ctx: &mut TypeContext<G>,
    op: &BinOp,
    left_ty: &Type,
    right_ty: &Type,
) -> Result<Type, TypeError> {
    use BinOp::*;
    ctx.unify(left_ty, right_ty)?;
    match op {
        Add | Sub | Mul | Div => {
            if left_ty.is_numeric() {
                Ok(left_ty.clone())
            } else {
                Err(GenericError)
            }
        }
        Eq | Ne => Ok(Type::Lit(LitTy::Boolean)),
        Le | Ge | Gt | Lt => {
            if left_ty.is_numeric() {
                Ok(Type::Lit(LitTy::Boolean))
            } else {
                Err(GenericError)
            }
        }
        And | Or | Impl => {
            ctx.unify(left_ty, &Type::Lit(LitTy::Boolean))?;
            Ok(Type::Lit(LitTy::Boolean))
        }
    }
}

fn typecheck_lit(lit: &Literal) -> LitTy {
    use LitTy::*;
    use Literal::*;

    match lit {
        U32(_) => Unsigned(Size::ThirtyTwo),
        U64(_) => Unsigned(Size::SixtyFour),
        Usize(_) => Unsigned(Size::Mach),
        U8(_) => Unsigned(Size::Eight),
        U16(_) => Unsigned(Size::Sixteen),
        Int(_) => Integer,
        F32(_) => Float,
        F64(_) => Double,
        Bool(_) => Boolean,
    }
}

#[cfg(test)]
mod check {
    use super::*;

    struct DummyG;

    impl GlobalContext for DummyG {
        fn resolve_name(&self, _: &Name) -> Option<Type> {
            None
        }

        fn constructor_type(&self, _: &Name) -> Option<(Vec<Type>, Type)> {
            None
        }
    }
    use crate::term::{BinOp::*, LitTy::*, Literal::*, Term::*, Type};

    #[test]
    fn test_simple() {
        let mut ctx = TypeContext::new(DummyG);
        check_term(
            &mut ctx,
            &mut Binary { left: box Lit { lit: U32(0) }, op: Add, right: box Lit { lit: U32(10) } },
            &Type::Lit(LitTy::Unsigned(Size::ThirtyTwo)),
        )
        .unwrap();
    }

    #[test]
    fn test_failure() {
        let mut ctx = TypeContext::new(DummyG);
        assert!(check_term(
            &mut ctx,
            &mut Binary {
                left: box Lit { lit: U32(0) },
                op: Add,
                right: box Lit { lit: Bool(true) }
            },
            &Type::Lit(LitTy::Signed(Size::ThirtyTwo)),
        )
        .is_err());
    }

    #[test]
    fn test_tuple() {
        let mut ctx = TypeContext::new(DummyG);
        ctx.register_var(
            &Ident("x".into()),
            Type::Tuple { elems: vec![Type::Lit(Boolean), Type::Lit(Boolean)] },
        );

        impl crate::parser::Resolver for DummyG {
            fn resolve(&self, _: &[String]) -> Option<Name> {
                Some(Name::Ident("x".into()))
            }
        }
        let mut p: Term =
            Term::from_syn(&DummyG, syn::parse_str("x == (true, false)").unwrap()).unwrap();
        let res = check_term(&mut ctx, &mut p, &Type::Lit(Boolean));

        assert_eq!(res, Ok(()));
    }
}
