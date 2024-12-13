use crate::*;
use ::std::borrow::Borrow;

// "In particular Eq, Ord and Hash must be equivalent for borrowed and owned values:
// x.borrow() == y.borrow() should give the same result as x == y."
// https://doc.rust-lang.org/std/borrow/trait.Borrow.html

extern_spec! {
    mod std {
        mod borrow {
            trait Borrow<Borrowed>
            where Borrowed: ?Sized
            {
                #[ensures(result.deep_model() == self.deep_model())]
                fn borrow(&self) -> &Borrowed
                where
                    Self: DeepModel,
                    Borrowed: DeepModel<DeepModelTy = Self::DeepModelTy>;
            }
        }
    }
}
