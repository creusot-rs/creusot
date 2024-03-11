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
pub struct CrErr;

impl From<CrErr> for Error {
    fn from(_: CrErr) -> Error {
        Error::new(DUMMY_SP, "internal error")
    }
}

impl std::fmt::Display for CrErr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "encountered errors during translation")
    }
}
impl std::error::Error for CrErr {}
