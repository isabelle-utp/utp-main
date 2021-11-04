signature Trac_TOKENS =
sig
type ('a,'b) token
type svalue
val ATTACK: (string) *  'a * 'a -> (svalue,'a) token
val ZERO: (string) *  'a * 'a -> (svalue,'a) token
val ONE: (string) *  'a * 'a -> (svalue,'a) token
val INTEGER_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val LOWER_STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val UPPER_STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val STRING_LITERAL: (string) *  'a * 'a -> (svalue,'a) token
val DOUBLE_RARROW: (string) *  'a * 'a -> (svalue,'a) token
val DOUBLE_ASTERISK: (string) *  'a * 'a -> (svalue,'a) token
val ASTERISK: (string) *  'a * 'a -> (svalue,'a) token
val PAREN_CLOSE: (string) *  'a * 'a -> (svalue,'a) token
val PAREN_OPEN: (string) *  'a * 'a -> (svalue,'a) token
val COLON: (string) *  'a * 'a -> (svalue,'a) token
val WHERE: (string) *  'a * 'a -> (svalue,'a) token
val FIXEDPOINT: (string) *  'a * 'a -> (svalue,'a) token
val COMMA: (string) *  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature Trac_LRVALS=
sig
structure Tokens : Trac_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
