pub mod function;
pub mod traits;
pub mod specification;
pub mod ty;
pub mod constant;

mod logic;
mod r#extern;

pub use logic::translate_logic;
pub use r#extern::translate_extern;
pub use function::translate_function;