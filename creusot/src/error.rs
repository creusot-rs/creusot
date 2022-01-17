use rustc_errors::DiagnosticId;
use rustc_session::Session;
use rustc_span::Span;

pub type CreusotResult<T> = Result<T, Error>;

// TODO: make this a vector of spans and strings
#[derive(Debug)]
pub struct Error {
    span: Span,
    msg: String,
}

impl Error {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Error { span, msg: msg.into() }
    }

    pub fn emit(self, sess: &Session) -> ! {
        sess.span_fatal_with_code(
            self.span,
            &self.msg,
            DiagnosticId::Error(String::from("creusot")),
        )
    }
}
