use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, DUMMY_SP};

pub type CreusotResult<T> = Result<T, Error>;

pub(crate) enum Error {
    MustPrint(Message),
    TypeCheck(CannotFetchThir),
}

// TODO: make this a vector of spans and strings
#[derive(Debug)]
pub struct Message {
    span: Span,
    msg: String,
}

impl Message {
    pub(crate) fn new(span: Span, msg: impl Into<String>) -> Self {
        Self { span, msg: msg.into() }
    }

    pub(crate) fn emit(self, tcx: TyCtxt) -> ! {
        // TODO: try to add a code back in
        tcx.dcx().span_fatal(self.span, self.msg)
    }
}

impl Error {
    pub(crate) fn msg(span: Span, msg: impl Into<String>) -> Self {
        Self::MustPrint(Message { span, msg: msg.into() })
    }
}

impl From<Message> for Error {
    fn from(value: Message) -> Self {
        Self::MustPrint(value)
    }
}
impl From<CannotFetchThir> for Error {
    fn from(value: CannotFetchThir) -> Self {
        Self::TypeCheck(value)
    }
}

/// This error is raised when fetching a function's THIR failed, because of a typechecking error.
///
/// It should usually be bubbled up to the caller, which should then throw it away and
/// proceed to call `tcx.dcx().abort_if_errors()`.
pub(crate) struct CannotFetchThir;

#[derive(Debug, Clone)]
pub struct InternalError(pub &'static str);

impl From<InternalError> for Error {
    fn from(err: InternalError) -> Error {
        Error::MustPrint(Message::new(DUMMY_SP, format!("internal error: {}", err.0)))
    }
}

impl std::fmt::Display for InternalError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "encountered errors during translation: '{}'", self.0)
    }
}
impl std::error::Error for InternalError {}
