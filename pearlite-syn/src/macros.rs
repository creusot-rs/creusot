macro_rules! ast_struct {
    (
        [$($attrs_pub:tt)*]
        struct $name:ident #full $($rest:tt)*
    ) => {
        #[cfg(feature = "full")]
        #[derive(Debug)]
        $($attrs_pub)* struct $name $($rest)*

        #[cfg(not(feature = "full"))]
        $($attrs_pub)* struct $name {
            _noconstruct: ::std::marker::PhantomData<::proc_macro2::Span>,
        }

        #[cfg(all(not(feature = "full"), feature = "printing"))]
        impl ::quote::ToTokens for $name {
            fn to_tokens(&self, _: &mut ::proc_macro2::TokenStream) {
                unreachable!()
            }
        }
    };

    (
        [$($attrs_pub:tt)*]
        struct $name:ident $($rest:tt)*
    ) => {
        #[derive(Debug)]
        $($attrs_pub)* struct $name $($rest)*
    };

    ($($t:tt)*) => {
        strip_attrs_pub!(ast_struct!($($t)*));
    };
}

macro_rules! ast_enum {
    (
        [$($attrs_pub:tt)*]
        enum $name:ident $($rest:tt)*
    ) => (
        $($attrs_pub)* enum $name $($rest)*
    );

    ($($t:tt)*) => {
        strip_attrs_pub!(ast_enum!($($t)*));
    };
}

macro_rules! ast_enum_of_structs {
    (
        $(#[$enum_attr:meta])*
        $pub:ident $enum:ident $name:ident $body:tt
        $($remaining:tt)*
    ) => {
        ast_enum!($(#[$enum_attr])* $pub $enum $name $body);
        ast_enum_of_structs_impl!($pub $enum $name $body $($remaining)*);
    };
}

macro_rules! ast_enum_of_structs_impl {
    (
        $pub:ident $enum:ident $name:ident {
            $(
                $(#[$variant_attr:meta])*
                $variant:ident $( ($($member:ident)::+) )*,
            )*
        }

        $($remaining:tt)*
    ) => {
        check_keyword_matches!(pub $pub);
        check_keyword_matches!(enum $enum);

        $($(
            ast_enum_from_struct!($name::$variant, $($member)::+);
        )*)*

        #[cfg(feature = "printing")]
        generate_to_tokens! {
            $($remaining)*
            ()
            tokens
            $name { $($variant $($($member)::+)*,)* }
        }

        generate_debug!  {
            $($remaining)*
            ()
            f
            $name { $($variant $($($member)::+)*,)* }
        }
    };
}

macro_rules! ast_enum_from_struct {
    // No From<TokenStream> for verbatim variants.
    ($name:ident::Verbatim, $member:ident) => {};

    ($name:ident::$variant:ident, $member:ident) => {
        impl From<$member> for $name {
            fn from(e: $member) -> $name {
                $name::$variant(e)
            }
        }
    };
}

#[cfg(feature = "printing")]
macro_rules! generate_to_tokens {
    (($($arms:tt)*) $tokens:ident $name:ident { $variant:ident, $($next:tt)*}) => {
        generate_to_tokens!(
            ($($arms)* $name::$variant => {})
            $tokens $name { $($next)* }
        );
    };

    (($($arms:tt)*) $tokens:ident $name:ident { $variant:ident $member:ident, $($next:tt)*}) => {
        generate_to_tokens!(
            ($($arms)* $name::$variant(_e) => _e.to_tokens($tokens),)
            $tokens $name { $($next)* }
        );
    };

    (($($arms:tt)*) $tokens:ident $name:ident {}) => {
        impl ::quote::ToTokens for $name {
            fn to_tokens(&self, $tokens: &mut ::proc_macro2::TokenStream) {
                match self {
                    $($arms)*
                }
            }
        }
    };
}

macro_rules! generate_debug {
    (($($arms:tt)*) $f:ident $name:ident { $variant:ident, $($next:tt)*}) => {
        generate_debug!(
            ($($arms)* $name::$variant => { Ok(()) })
            $f $name { $($next)* }
        );
    };

    (($($arms:tt)*) $f:ident $name:ident { $variant:ident $member:ident, $($next:tt)*}) => {
        generate_debug!(
            ($($arms)* $name::$variant(_e) => std::fmt::Debug::fmt(&_e, $f),)
            $f $name { $($next)* }
        );
    };

    (($($arms:tt)*) $f:ident $name:ident {}) => {
        impl std::fmt::Debug for $name {
            fn fmt(&self, $f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $($arms)*
                }
            }
        }
    };
}

macro_rules! strip_attrs_pub {
    ($mac:ident!($(#[$m:meta])* $pub:ident $($t:tt)*)) => {
        check_keyword_matches!(pub $pub);

        $mac!([$(#[$m])* $pub] $($t)*);
    };
}

macro_rules! check_keyword_matches {
    (enum enum) => {};
    (pub pub) => {};
}
