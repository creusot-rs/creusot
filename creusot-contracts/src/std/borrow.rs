use crate::*;
use ::std::borrow::Borrow;

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
