module Lex : sig
  val new_line : Lexing.lexbuf -> unit
  val line_incs : Lexing.lexbuf -> unit
end

module Async : sig
  val async : 'a Lwt.t -> 'a
  val async_handler : (unit -> 'a) -> 'a Lwt.t
end
