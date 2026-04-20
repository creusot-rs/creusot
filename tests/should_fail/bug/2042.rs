use creusot_std::prelude::*;

pub struct S((Int, Int));

impl S {
    #[logic(open)]
    pub fn get(self) -> Int {
        self.0.1
    }
}
