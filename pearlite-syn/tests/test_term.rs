#[macro_use]
mod macros;

use pearlite_syn::Term;
use quote::quote;

#[test]
fn test_impl() {
    snapshot!(quote!(false ==> true) as Term, @r###"
    TermImpl {
        hyp: TermLit {
            lit: Bool(
                LitBool {
                    value: false,
                },
            ),
        },
        eqeq_token: EqEq,
        gt_token: Gt,
        cons: TermLit {
            lit: Bool(
                LitBool {
                    value: true,
                },
            ),
        },
    }
    "###);
}

#[test]
fn test_final() {
    snapshot!(quote!(^a) as Term, @r###"
    TermFinal {
        final_token: Caret,
        term: TermPath {
            inner: ExprPath {
                attrs: [],
                qself: None,
                path: Path {
                    leading_colon: None,
                    segments: [
                        PathSegment {
                            ident: Ident(
                                a,
                            ),
                            arguments: None,
                        },
                    ],
                },
            },
        },
    }
    "###);
}

#[test]
fn test_model() {
    snapshot!(quote!(a@) as Term, @r###"
    TermModel {
        term: TermPath {
            inner: ExprPath {
                attrs: [],
                qself: None,
                path: Path {
                    leading_colon: None,
                    segments: [
                        PathSegment {
                            ident: Ident(
                                a,
                            ),
                            arguments: None,
                        },
                    ],
                },
            },
        },
        at_token: At,
    }"###);
}

#[test]
fn test_forall() {
    snapshot!(quote!(forall<x : u32> true) as Term, @r###"
    TermForall {
        forall_token: Keyword [forall],
        lt_token: Lt,
        args: [
            QuantArg {
                ident: Ident(
                    x,
                ),
                colon_token: Colon,
                ty: Path(
                    TypePath {
                        qself: None,
                        path: Path {
                            leading_colon: None,
                            segments: [
                                PathSegment {
                                    ident: Ident(
                                        u32,
                                    ),
                                    arguments: None,
                                },
                            ],
                        },
                    },
                ),
            },
        ],
        gt_token: Gt,
        term: TermLit {
            lit: Bool(
                LitBool {
                    value: true,
                },
            ),
        },
    }
    "###);
}

#[test]
fn test_exists() {
    snapshot!(quote!(exists<x : u32> true) as Term, @r###"
    TermExists {
        exists_token: Keyword [exists],
        lt_token: Lt,
        args: [
            QuantArg {
                ident: Ident(
                    x,
                ),
                colon_token: Colon,
                ty: Path(
                    TypePath {
                        qself: None,
                        path: Path {
                            leading_colon: None,
                            segments: [
                                PathSegment {
                                    ident: Ident(
                                        u32,
                                    ),
                                    arguments: None,
                                },
                            ],
                        },
                    },
                ),
            },
        ],
        gt_token: Gt,
        term: TermLit {
            lit: Bool(
                LitBool {
                    value: true,
                },
            ),
        },
    }
    "###);
}

#[test]
fn test_absurd() {
    snapshot!(quote!(absurd) as Term, @r###"
    TermAbsurd {
        absurd_token: Keyword [absurd],
    }
    "###);
}

#[test]
fn test_pearlite() {
    snapshot!(quote!(pearlite!{ x }) as Term, @r###"
    TermPearlite {
        pearlite_token: Keyword [pearlite],
        bang_token: Bang,
        block: TBlock {
            brace_token: Brace,
            stmts: [
                Expr(
                    TermPath {
                        inner: ExprPath {
                            attrs: [],
                            qself: None,
                            path: Path {
                                leading_colon: None,
                                segments: [
                                    PathSegment {
                                        ident: Ident(
                                            x,
                                        ),
                                        arguments: None,
                                    },
                                ],
                            },
                        },
                    },
                ),
            ],
        },
    }
    "###);
}

#[test]
fn test_match() {
    snapshot!(quote!(match x {
        Some(x) => true,
        None => false
    }) as Term, @r###"
    TermMatch {
        match_token: Match,
        expr: TermPath {
            inner: ExprPath {
                attrs: [],
                qself: None,
                path: Path {
                    leading_colon: None,
                    segments: [
                        PathSegment {
                            ident: Ident(
                                x,
                            ),
                            arguments: None,
                        },
                    ],
                },
            },
        },
        brace_token: Brace,
        arms: [
            TermArm {
                pat: TupleStruct(
                    PatTupleStruct {
                        attrs: [],
                        path: Path {
                            leading_colon: None,
                            segments: [
                                PathSegment {
                                    ident: Ident(
                                        Some,
                                    ),
                                    arguments: None,
                                },
                            ],
                        },
                        pat: PatTuple {
                            attrs: [],
                            paren_token: Paren,
                            elems: [
                                Ident(
                                    PatIdent {
                                        attrs: [],
                                        by_ref: None,
                                        mutability: None,
                                        ident: Ident(
                                            x,
                                        ),
                                        subpat: None,
                                    },
                                ),
                            ],
                        },
                    },
                ),
                guard: None,
                fat_arrow_token: FatArrow,
                body: TermLit {
                    lit: Bool(
                        LitBool {
                            value: true,
                        },
                    ),
                },
                comma: Some(
                    Comma,
                ),
            },
            TermArm {
                pat: Ident(
                    PatIdent {
                        attrs: [],
                        by_ref: None,
                        mutability: None,
                        ident: Ident(
                            None,
                        ),
                        subpat: None,
                    },
                ),
                guard: None,
                fat_arrow_token: FatArrow,
                body: TermLit {
                    lit: Bool(
                        LitBool {
                            value: false,
                        },
                    ),
                },
                comma: None,
            },
        ],
    }
    "###);
}
