# Why3 

A Rust library furnishing the Why3 AST used by the Creusot verifier, and its associated pretty printer. 
The library supports two input formats to why3: WhyML (`.mlw`), [Coma](https://coma.paulpatault.fr/) (`.coma`).

As it stands the core Why3 `Exp` type is heavily burdened with tech debt associated to its evolution as an offsprout of creusot. 
I hope to clean this up incrementally, but if you are planning on using `why3` in a project, please contact me so I can reprioritize. 

