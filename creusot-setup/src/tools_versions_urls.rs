// "known good" versions and URLs for downloading binary releases

// NOTE: when ugrading a binary to a newer version:
// - update its [FOO_VERSION] below
// - update its URL in each [URLS] block below
// - update the SHA256 hash for each binary accordingly (use e.g. sha256sum to compute it)

// tools without binary releases
pub const WHY3_VERSION: &'static str = "1.8.2";
pub const WHY3_CONFIG_MAGIC_NUMBER: &'static str = "14";
pub const WHY3FIND_VERSION: &'static str = "1.2.0";
// tools with binary releases
pub const ALTERGO_VERSION: &'static str = "2.6.2";
pub const Z3_VERSION: &'static str = "4.15.3";
pub const CVC4_VERSION: &'static str = "1.8";
pub const CVC5_VERSION: &'static str = "1.3.1";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub const URLS: Urls = Urls {
    altergo: Url {
        url: "https://github.com/OCamlPro/alt-ergo/releases/download/v2.6.2/alt-ergo-v2.6.2-x86_64-linux-musl",
        sha256: "bdc4e487f2bdfd421011c82f545df3f50530aee6d6e406b1e847d433650ca3c1",
    },
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.15.3/z3-4.15.3-x64-glibc-2.39.zip",
        sha256: "94549c5e31a75b9c543fe6eea8f32927054765c2e92e696d2d6dde0eedf348a1",
    },
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt",
        sha256: "d38a79cf984592785eda41ec888d94ca107ac1f13058740238041e28c8472e51",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.1/cvc5-Linux-x86_64-static-gpl.zip",
        sha256: "dcad9de0827509e8517f60da87f0c4292652627641dbcad8012644b6a982a183",
    },
};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub const URLS: Urls = Urls {
    altergo: Url {
        url: "https://github.com/OCamlPro/alt-ergo/releases/download/v2.6.2/alt-ergo-v2.6.2-aarch64-macos",
        sha256: "bfec57500243a3cf1d3b613662f5814492d49152453409a9a46d0dfeacf61b31",
    },
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.15.3/z3-4.15.3-arm64-osx-13.7.6.zip",
        sha256: "941659417b5464a361c49089658509f3118a0c3e8d4f8a1dc999f8b5cd1f3c71",
    },
    // CVC4 only has a macos x86_64 binary; we rely on rosetta for compatibility
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-macos-opt",
        sha256: "b8a0b8714dd947aa46182402d9caba27d3d696041e17704884bc3d8510066527",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.1/cvc5-macOS-arm64-static-gpl.zip",
        sha256: "e28df7104ebac5ca0953a0e9aadd016c2c63b00ec6edc3d25820fd888e7e22c3",
    },
};

pub struct Urls {
    pub altergo: Url,
    pub z3: Url,
    pub cvc4: Url,
    pub cvc5: Url,
}

pub struct Url {
    pub url: &'static str,
    pub sha256: &'static str,
}
