/* This is a modified version of the default rust.js in highlight.js (licensed under BSD3).
   It is extended with rules for highlighting Creusot annotations (requires, ensures, invariant, etc.).

   Build instructions:
   1. git clone https://github.com/highlightjs/highlight.js
   2. cd highlight.js
   3. ln -s /path/to/creusot/guide/highlight.js extra/creusot
   4. npm install
   5. node tools/build.js -t browser rust pearlite
   6. cp build/highlight.min.js /path/to/creusot/guide/theme/highlight.js
*/

export const NUMBER_SUFFIX = '([ui](8|16|32|64|128|size)|f(32|64)|int)\?';
export const KEYWORDS = [
  "abstract",
  "as",
  "async",
  "await",
  "become",
  "box",
  "break",
  "const",
  "continue",
  "crate",
  "do",
  "dyn",
  "else",
  "enum",
  "extern",
  "final",
  "fn",
  "for",
  "if",
  "impl",
  "in",
  "let",
  "loop",
  "macro",
  "match",
  "mod",
  "move",
  "mut",
  "override",
  "priv",
  "pub",
  "ref",
  "return",
  "self",
  "Self",
  "static",
  "struct",
  "super",
  "trait",
  "try",
  "type",
  "typeof",
  "union",
  "unsafe",
  "unsized",
  "use",
  "virtual",
  "where",
  "while",
  "yield"
];
export const LITERALS = [
  "true",
  "false",
  "Some",
  "None",
  "Ok",
  "Err"
];
export const TYPES = [
  "i8",
  "i16",
  "i32",
  "i64",
  "i128",
  "isize",
  "u8",
  "u16",
  "u32",
  "u64",
  "u128",
  "usize",
  "f32",
  "f64",
  "str",
  "char",
  "bool",
  "Box",
  "Option",
  "Result",
  "String",
  "Vec",
];
export const CREUSOT_TYPES = [
  "DeepModel",
  "FMap",
  "FSet",
  "Ghost",
  "Id",
  "Int",
  "Invariant",
  "Mapping",
  "PermCell",
  "PermCellOwn",
  "PeanoInt",
  "PredCell",
  "PtrOwn",
  "Real",
  "Resolve",
  "Seq",
  "Set",
  "Snapshot",
  "View",
];
export const PEARLITE_KEYWORDS = ["forall", "exists"].concat(KEYWORDS);
export function utils(hljs) {
  const FUNCTION_INVOKE = {
      className: "title.function.invoke",
      relevance: 0,
      begin: hljs.regex.concat(
        /\b/,
        /(?!(?:let|for|while|if|else|match)\b)/,
        hljs.IDENT_RE,
        hljs.regex.lookahead(/\s*\(/))
  };
  const PEARLITE = [
    hljs.C_LINE_COMMENT_MODE,
    hljs.COMMENT('/\\*', '\\*/', { contains: [ 'self' ] }),
    {
      scope: "number",
      variants: [
        { begin: '\\b0b([01_]+)' + NUMBER_SUFFIX },
        { begin: '\\b0o([0-7_]+)' + NUMBER_SUFFIX },
        { begin: '\\b0x([A-Fa-f0-9_]+)' + NUMBER_SUFFIX },
        { begin: '\\b(\\d[\\d_]*(\\.[0-9_]+)?([eE][+-]?[0-9_]+)?)'
                + NUMBER_SUFFIX }
      ],
    },
    FUNCTION_INVOKE
  ];
  return {
    pearlite: PEARLITE,
  }
}

/** @type LanguageFn */

export default function(hljs) {
  const UTILS = utils(hljs);
  const PEARLITE = UTILS.pearlite;
  const regex = hljs.regex;
  // ============================================
  // Added to support the r# keyword, which is a raw identifier in Rust.
  const RAW_IDENTIFIER = /(r#)?/;
  const UNDERSCORE_IDENT_RE = regex.concat(RAW_IDENTIFIER, hljs.UNDERSCORE_IDENT_RE);
  const IDENT_RE = regex.concat(RAW_IDENTIFIER, hljs.IDENT_RE);
  // ============================================
  const FUNCTION_INVOKE = {
    className: "title.function.invoke",
    relevance: 0,
    begin: regex.concat(
      /\b/,
      /(?!(?:let|for|while|if|else|match)\b)/,
      IDENT_RE,
      regex.lookahead(/\s*\(/))
  };
  const BUILTINS = [
    // functions
    'drop ',
    // traits
    "Copy",
    "Send",
    "Sized",
    "Sync",
    "Drop",
    "Fn",
    "FnMut",
    "FnOnce",
    "ToOwned",
    "Clone",
    "Debug",
    "PartialEq",
    "PartialOrd",
    "Eq",
    "Ord",
    "AsRef",
    "AsMut",
    "Into",
    "From",
    "Default",
    "Iterator",
    "Extend",
    "IntoIterator",
    "DoubleEndedIterator",
    "ExactSizeIterator",
    "SliceConcatExt",
    "ToString",
    // macros
    "assert!",
    "assert_eq!",
    "bitflags!",
    "bytes!",
    "cfg!",
    "col!",
    "concat!",
    "concat_idents!",
    "debug_assert!",
    "debug_assert_eq!",
    "env!",
    "eprintln!",
    "panic!",
    "file!",
    "format!",
    "format_args!",
    "include_bytes!",
    "include_str!",
    "line!",
    "local_data_key!",
    "module_path!",
    "option_env!",
    "print!",
    "println!",
    "select!",
    "stringify!",
    "try!",
    "unimplemented!",
    "unreachable!",
    "vec!",
    "write!",
    "writeln!",
    "macro_rules!",
    "assert_ne!",
    "debug_assert_ne!"
  ];
  return {
    name: 'Rust',
    aliases: [ 'rs' ],
    keywords: {
      $pattern: hljs.IDENT_RE + '!?',
      type: TYPES,
      'creusot-type': CREUSOT_TYPES,
      keyword: KEYWORDS,
      literal: LITERALS,
      built_in: BUILTINS
    },
    illegal: '</',
    contains: [
      hljs.C_LINE_COMMENT_MODE,
      hljs.COMMENT('/\\*', '\\*/', { contains: [ 'self' ] }),
      hljs.inherit(hljs.QUOTE_STRING_MODE, {
        begin: /b?"/,
        illegal: null
      }),
      {
        className: 'symbol',
        // negative lookahead to avoid matching `'`
        begin: /'[a-zA-Z_][a-zA-Z0-9_]*(?!')/
      },
      {
        scope: 'string',
        variants: [
          { begin: /b?r(#*)"(.|\n)*?"\1(?!#)/ },
          {
            begin: /b?'/,
            end: /'/,
            contains: [
              {
                scope: "char.escape",
                match: /\\('|\w|x\w{2}|u\w{4}|U\w{8})/
              }
            ]
          }
        ]
      },
      {
        className: 'number',
        variants: [
          { begin: '\\b0b([01_]+)' + NUMBER_SUFFIX },
          { begin: '\\b0o([0-7_]+)' + NUMBER_SUFFIX },
          { begin: '\\b0x([A-Fa-f0-9_]+)' + NUMBER_SUFFIX },
          { begin: '\\b(\\d[\\d_]*(\\.[0-9_]+)?([eE][+-]?[0-9_]+)?)'
                   + NUMBER_SUFFIX }
        ],
        relevance: 0
      },
      {
        begin: [
          /fn/,
          /\s+/,
          UNDERSCORE_IDENT_RE
        ],
        className: {
          1: "keyword",
          3: "title.function"
        }
      },
      {
        scope: 'keyword.creusot',
        match: /\bghost\s*!/
      },
      {
        className: 'meta',
        begin: '#!?\\[',
        end: '\\]',
        keywords: {
          'keyword.creusot': ["law", "logic", "check", "open", "prophetic", "terminates", "trusted", "ghost"]
        },
        contains: [
          {
            scope: 'creusot',
            begin: /(?:requires|ensures|invariant|variant)\(/,
            beginScope: "keyword.creusot",
            endScope: "keyword.creusot",
            // Hack to handle nested parentheses: use the `end` regex to match all parentheses and keep track of the nesting,
            // calling `response.ignoreMatch()` as long as we haven't reached the end.
            // Doing this because highlight.js's support for nested brackets seems awfully limited.
            end: /[()]/,
            "on:begin": function (matchData, response) {
              response.data.nesting = 0;
            },
            "on:end": function (matchData, response) {
              if (matchData[0] === '(') {
                response.data.nesting++;
                response.ignoreMatch();
              } else if (response.data.nesting !== 0) {
                response.data.nesting--;
                response.ignoreMatch();
              }
            },
            literals: LITERALS,
            contains: PEARLITE,
            keywords: PEARLITE_KEYWORDS
          },
          {
            className: 'string',
            begin: /"/,
            end: /"/,
            contains: [
              hljs.BACKSLASH_ESCAPE
            ]
          }
        ]
      },
      {
        scope: 'creusot',
        beginScope: "keyword.creusot",
        endScope: "keyword.creusot",
        contains: PEARLITE,
        keywords: PEARLITE_KEYWORDS,
        // See note above.
        "on:begin": function (matchData, response) {
          response.data.nesting = 0;
        },
        "on:end": function (matchData, response) {
          if (matchData[0] === '(' || matchData[0] === '[' || matchData[0] === '{') {
            response.data.nesting++;
            response.ignoreMatch();
          } else if (response.data.nesting !== 0) {
            response.data.nesting--;
            response.ignoreMatch();
          }
        },
        variants: [
          { begin: /\b(?:snapshot|proof_assert|pearlite)\s*!\s*\(/, end: /[()]/ },
          { begin: /\b(?:snapshot|proof_assert|pearlite)\s*!\s*\[/, end: /[\[\]]/ },
          { begin: /\b(?:snapshot|proof_assert|pearlite)\s*!\s*{/, end: /[{}]/ }
        ]
      },
      {
        begin: [
          /let/,
          /\s+/,
          /(?:mut\s+)?/,
          UNDERSCORE_IDENT_RE
        ],
        className: {
          1: "keyword",
          3: "keyword",
          4: "variable"
        }
      },
      // must come before impl/for rule later
      {
        begin: [
          /for/,
          /\s+/,
          UNDERSCORE_IDENT_RE,
          /\s+/,
          /in/
        ],
        className: {
          1: "keyword",
          3: "variable",
          5: "keyword"
        }
      },
      {
        begin: [
          /type/,
          /\s+/,
          UNDERSCORE_IDENT_RE
        ],
        className: {
          1: "keyword",
          3: "title.class"
        }
      },
      {
        begin: [
          /(?:trait|enum|struct|union|impl|for)/,
          /\s+/,
          UNDERSCORE_IDENT_RE
        ],
        className: {
          1: "keyword",
          3: "title.class"
        }
      },
      {
        begin: hljs.IDENT_RE + '::',
        keywords: {
          keyword: "Self",
          built_in: BUILTINS,
          type: TYPES,
          'creusot-type': CREUSOT_TYPES,
        }
      },
      {
        className: "punctuation",
        begin: '->'
      },
      FUNCTION_INVOKE
    ]
  };
}
