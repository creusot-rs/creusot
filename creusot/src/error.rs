use rustc_errors::DiagnosticId;
use rustc_session::Session;
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

    pub(crate) fn emit(self, sess: &Session) -> ! {
        sess.span_fatal_with_code(self.span, self.msg, DiagnosticId::Error(String::from("creusot")))
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
