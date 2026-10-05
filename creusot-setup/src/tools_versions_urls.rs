// "known good" versions and URLs for downloading binary releases

// NOTE: when ugrading a binary to a newer version:
// - update its [FOO_VERSION] below
// - update its URL in each [URLS] block below
// - update the SHA256 hash for each binary accordingly (use e.g. sha256sum to compute it)

// tools without binary releases
pub const WHY3_VERSION: &'static str = "1.8.2"; // For the real version, see creusot-deps.opam
pub const WHY3_CONFIG_MAGIC_NUMBER: &'static str = "14";
pub const WHY3FIND_VERSION: &'static str = "1.3.0"; // For the real version, see creusot-deps.opam
// tools with binary releases
pub const ALTERGO_VERSION: &'static str = "2.6.4";
pub const Z3_VERSION: &'static str = "5.1.0";
pub const CVC4_VERSION: &'static str = "1.8";
pub const CVC5_VERSION: &'static str = "1.3.1";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub const URLS: Urls = Urls {
    altergo: Some(Url {
        url: "https://github.com/OCamlPro/alt-ergo/releases/download/v2.6.4/alt-ergo-v2.6.4-x86_64-linux-musl",
        sha256: "80d41dd9cf4b024be7412e499f81960ddc63978f5d78a29311a05aaab125681a",
    }),
    z3: Some(Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-x64-glibc-2.39.zip",
        sha256: "f47be8d27d3230e823bf1eeede2fe0abaca55bb78d0b59974370e6689a92284a",
    }),
    cvc4: Some(Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt",
        sha256: "d38a79cf984592785eda41ec888d94ca107ac1f13058740238041e28c8472e51",
    }),
    cvc5: Some(Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.1/cvc5-Linux-x86_64-static-gpl.zip",
        sha256: "dcad9de0827509e8517f60da87f0c4292652627641dbcad8012644b6a982a183",
    }),
};

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
pub const URLS: Urls = Urls {
    // Alt-Ergo publishes no aarch64-linux binary; it is an OCaml program, so
    // `opam install alt-ergo` plus `--external alt-ergo` covers it.
    altergo: None,
    z3: Some(Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-arm64-glibc-2.38.zip",
        sha256: "2832cfd43c6862fbaf78834b5f1e35d031b4a87e85456b696c1c6f609cd5609e",
    }),
    // CVC4 is archived upstream (last release 2020) and never shipped an
    // aarch64-linux binary. CVC5 supersedes it.
    cvc4: None,
    cvc5: Some(Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.1/cvc5-Linux-arm64-static-gpl.zip",
        sha256: "a3673b5f91aa71f11939494498ae7f8b89a035c7e0993f5a2f81728e6f9bcc43",
    }),
};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub const URLS: Urls = Urls {
    altergo: Some(Url {
        url: "https://github.com/OCamlPro/alt-ergo/releases/download/v2.6.4/alt-ergo-v2.6.4-aarch64-macos",
        sha256: "083d2d432d4954a2c234b1ca88a97b8c7e98bcbd3dcbae1753be401eb1633196",
    }),
    z3: Some(Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-arm64-osx-13.3.zip",
        sha256: "81d29e934fd863079a74af35eecaeaef8047e0e12414d33ca322b358d68383db",
    }),
    // CVC4 only has a macos x86_64 binary; we rely on rosetta for compatibility
    cvc4: Some(Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-macos-opt",
        sha256: "b8a0b8714dd947aa46182402d9caba27d3d696041e17704884bc3d8510066527",
    }),
    cvc5: Some(Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.1/cvc5-macOS-arm64-static-gpl.zip",
        sha256: "e28df7104ebac5ca0953a0e9aadd016c2c63b00ec6edc3d25820fd888e7e22c3",
    }),
};

/// A `None` field means: no binary release of that prover exists for this
/// platform. `creusot-install` skips it with a message; install it by other
/// means (opam, distro package, from source) and pass `--external <TOOL>`.
pub struct Urls {
    pub altergo: Option<Url>,
    pub z3: Option<Url>,
    pub cvc4: Option<Url>,
    pub cvc5: Option<Url>,
}

pub struct Url {
    pub url: &'static str,
    pub sha256: &'static str,
}
