signature TracTransaction_TOKENS =
sig
type ('a,'b) token
type svalue
val OF: (string) *  'a * 'a -> (svalue,'a) token
val STAR: (string) *  'a * 'a -> (svalue,'a) token
val INTEGER_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val UNDERSCORE: (string) *  'a * 'a -> (svalue,'a) token
val LOWER_STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val UPPER_STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val TRANSACTIONS: (string) *  'a * 'a -> (svalue,'a) token
val ANALYSIS: (string) *  'a * 'a -> (svalue,'a) token
val ARROW: (string) *  'a * 'a -> (svalue,'a) token
val SETS: (string) *  'a * 'a -> (svalue,'a) token
val TYPES: (string) *  'a * 'a -> (svalue,'a) token
val equal: (string) *  'a * 'a -> (svalue,'a) token
val QUESTION: (string) *  'a * 'a -> (svalue,'a) token
val slash: (string) *  'a * 'a -> (svalue,'a) token
val ATTACK: (string) *  'a * 'a -> (svalue,'a) token
val NEW: (string) *  'a * 'a -> (svalue,'a) token
val DELETE: (string) *  'a * 'a -> (svalue,'a) token
val INSERT: (string) *  'a * 'a -> (svalue,'a) token
val NOTIN: (string) *  'a * 'a -> (svalue,'a) token
val IN: (string) *  'a * 'a -> (svalue,'a) token
val SEND: (string) *  'a * 'a -> (svalue,'a) token
val RECEIVE: (string) *  'a * 'a -> (svalue,'a) token
val PRIVATE: (string) *  'a * 'a -> (svalue,'a) token
val PUBLIC: (string) *  'a * 'a -> (svalue,'a) token
val FUNCTIONS: (string) *  'a * 'a -> (svalue,'a) token
val Sets: (string) *  'a * 'a -> (svalue,'a) token
val TBETWEEN: (string) *  'a * 'a -> (svalue,'a) token
val TSECRET: (string) *  'a * 'a -> (svalue,'a) token
val ON: (string) *  'a * 'a -> (svalue,'a) token
val WEAKLY: (string) *  'a * 'a -> (svalue,'a) token
val AUTHENTICATES: (string) *  'a * 'a -> (svalue,'a) token
val GOALS: (string) *  'a * 'a -> (svalue,'a) token
val ABSTRACTION: (string) *  'a * 'a -> (svalue,'a) token
val ACTIONS: (string) *  'a * 'a -> (svalue,'a) token
val WHERE: (string) *  'a * 'a -> (svalue,'a) token
val KNOWLEDGE: (string) *  'a * 'a -> (svalue,'a) token
val PROTOCOL: (string) *  'a * 'a -> (svalue,'a) token
val UNION: (string) *  'a * 'a -> (svalue,'a) token
val CLOSESQB: (string) *  'a * 'a -> (svalue,'a) token
val OPENSQB: (string) *  'a * 'a -> (svalue,'a) token
val COMMA: (string) *  'a * 'a -> (svalue,'a) token
val DOT: (string) *  'a * 'a -> (svalue,'a) token
val EXCLAM: (string) *  'a * 'a -> (svalue,'a) token
val UNEQUAL: (string) *  'a * 'a -> (svalue,'a) token
val PERCENT: (string) *  'a * 'a -> (svalue,'a) token
val FSECCH: (string) *  'a * 'a -> (svalue,'a) token
val FAUTHCH: (string) *  'a * 'a -> (svalue,'a) token
val INSECCH: (string) *  'a * 'a -> (svalue,'a) token
val CONFCH: (string) *  'a * 'a -> (svalue,'a) token
val AUTHCH: (string) *  'a * 'a -> (svalue,'a) token
val SECCH: (string) *  'a * 'a -> (svalue,'a) token
val SEMICOLON: (string) *  'a * 'a -> (svalue,'a) token
val COLON: (string) *  'a * 'a -> (svalue,'a) token
val CLOSESCRYPT: (string) *  'a * 'a -> (svalue,'a) token
val OPENSCRYPT: (string) *  'a * 'a -> (svalue,'a) token
val CLOSEB: (string) *  'a * 'a -> (svalue,'a) token
val OPENB: (string) *  'a * 'a -> (svalue,'a) token
val CLOSEP: (string) *  'a * 'a -> (svalue,'a) token
val OPENP: (string) *  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature TracTransaction_LRVALS=
sig
structure Tokens : TracTransaction_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
