// "known good" versions and URLs for downloading binary releases

// NOTE: when ugrading a binary to a newer version:
// - update its [FOO_VERSION] below
// - update its URL in each [URLS] block below
// - update the SHA256 hash for each binary accordingly (use e.g. sha256sum to compute it)

// tools without binary releases
pub const WHY3_VERSION: &'static str = "1.7.2";
pub const WHY3_CONFIG_MAGIC_NUMBER: &'static str = "14";
pub const ALTERGO_VERSION: &'static str = "2.5.3";
// tools with binary releases
pub const Z3_VERSION: &'static str = "4.12.4";
pub const CVC4_VERSION: &'static str = "1.8";
pub const CVC5_VERSION: &'static str = "1.0.5";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub const URLS: Urls = Urls {
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-x64-glibc-2.35.zip",
        sha256: "e23d3a5670dc83285f581c2610e9cf701bb22db09b5336d85a4df743253b2335",
    },
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt",
        sha256: "d38a79cf984592785eda41ec888d94ca107ac1f13058740238041e28c8472e51",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-Linux",
        sha256: "57fa94b740e0827f655a731b97dae84fedf86e65fa897c3a56a01a83d283d15e",
    }
};

#[cfg(all(target_os = "macos", target_arch = "x86_64"))]
pub const URLS: Urls = Urls {
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-x64-osx-11.7.10.zip",
        sha256: "0e6da979dc6ec501ad878d962802d20aff465ac0c24e4c1234169f3e92a0e6a3",
    },
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-macos-opt",
        sha256: "b8a0b8714dd947aa46182402d9caba27d3d696041e17704884bc3d8510066527",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-macOS",
        sha256: "0e74e40a3db82f3ac4d8ea23308931bedbc6afbcf3ed484b8b000da17c75885c",
    }
};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub const URLS: Urls = Urls {
    z3: Url {
        url: "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-arm64-osx-11.0.zip",
        sha256: "ab6798a9a85f406d7db9eb1fe692ff3db78155c509f71d0cae5933f4c47b5a38",
    },
    // CVC4 only has a macos x86_64 binary; we rely on rosetta for compatibility
    cvc4: Url {
        url: "https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-macos-opt",
        sha256: "b8a0b8714dd947aa46182402d9caba27d3d696041e17704884bc3d8510066527",
    },
    cvc5: Url {
        url: "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-macOS-arm64",
        sha256: "f1fe16664d88f9549da3df00853b6ddabafa68b1dc1c62d6dad0c0549cf95a33",
    }
};

pub struct Urls {
    pub z3: Url,
    pub cvc4: Url,
    pub cvc5: Url,
}

pub struct Url {
    pub url: &'static str,
    pub sha256: &'static str,
}
