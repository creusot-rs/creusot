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
pub const Z3_VERSION: &'static str = "4.15.4";
pub const CVC4_VERSION: &'static str = "1.8";
pub const CVC5_VERSION: &'static str = "1.3.2";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub const URLS: Urls = Urls {
    altergo: Url {
        url: "https://github.com/OCamlPro/alt-ergo/releases/download/v2.6.2/alt-ergo-v2.6.2-x86_64-linux-musl",
        sha256: "bdc4e487f2bdfd421011c82f545df3f50530aee6d6e406b1e847d433650ca3c1",
    },
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.15.4/z3-4.15.4-x64-glibc-2.39.zip",
        sha256: "a41b690e89c343931471506cdc6d957b6044a200fd2d240cc017432afdff7d3e",
    },
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt",
        sha256: "d38a79cf984592785eda41ec888d94ca107ac1f13058740238041e28c8472e51",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.2/cvc5-Linux-x86_64-static-gpl.zip",
        sha256: "30abf22d8042f3c4d3eb1120c595abd461f92f276a6d1264895fb4403b5fb3fd",
    },
};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub const URLS: Urls = Urls {
    altergo: Url {
        url: "https://github.com/OCamlPro/alt-ergo/releases/download/v2.6.2/alt-ergo-v2.6.2-aarch64-macos",
        sha256: "bfec57500243a3cf1d3b613662f5814492d49152453409a9a46d0dfeacf61b31",
    },
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.15.4/z3-4.15.4-arm64-osx-13.7.6.zip",
        sha256: "8bb3439772cafd75240d61abf255e89122850bab93563d1283b048359ab4e88f",
    },
    // CVC4 only has a macos x86_64 binary; we rely on rosetta for compatibility
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-macos-opt",
        sha256: "b8a0b8714dd947aa46182402d9caba27d3d696041e17704884bc3d8510066527",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.2/cvc5-macOS-arm64-static-gpl.zip",
        sha256: "6c63ba3bd174d026be161be75f64df8d200c8a284012c49e91807f3ede5afc44",
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
