use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, DUMMY_SP};

pub type CreusotResult<T> = Result<T, Error>;

// TODO: make this a vector of spans and strings
#[derive(Debug)]
pub struct Error {
    span: Span,
    msg: String,
}

impl Error {
    pub(crate) fn new(span: Span, msg: impl Into<String>) -> Self {
        Error { span, msg: msg.into() }
    }

    pub(crate) fn emit(self, tcx: TyCtxt) -> ! {
        // TODO: try to add a code back in
        tcx.dcx().span_fatal(self.span, self.msg)
    }
}

#[derive(Debug, Clone)]
pub struct InternalError(pub &'static str);

impl From<InternalError> for Error {
    fn from(err: InternalError) -> Error {
        Error::new(DUMMY_SP, format!("internal error: {}", err.0))
    }
}

impl std::fmt::Display for InternalError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "encountered errors during translation: '{}'", self.0)
    }
}
impl std::error::Error for InternalError {}
