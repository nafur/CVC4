from pygments.lexer import RegexLexer
from pygments import token

class SmtLibLexer(RegexLexer):

    name = 'smtlib'

    tokens = {
        'root': [
            (r'QF_BV', token.Text),
            (r'QF_UFDT', token.Text),
            (r'ALL_SUPPORTED', token.Text),
            (r'set-logic', token.Keyword),
            (r'set-option', token.Keyword),
            (r'declare-codatatypes', token.Keyword),
            (r'declare-const', token.Keyword),
            (r'declare-datatypes', token.Keyword),
            (r'declare-fun', token.Keyword),
            (r'define-fun', token.Keyword),
            (r'assert\b', token.Keyword),
            (r'check-sat-assuming', token.Keyword),
            (r'check-sat', token.Keyword),
            (r'exit', token.Keyword),
            (r'get-model', token.Keyword),
            (r'get-unsat-assumptions', token.Keyword),
            (r'get-unsat-core', token.Keyword),
            (r'push', token.Keyword),
            (r'pop', token.Keyword),
            (r'as', token.Name.Attribute),
            (r':incremental', token.Name.Attribute),
            (r':named', token.Name.Attribute),
            (r':produce-models', token.Name.Attribute),
            (r':produce-unsat-cores', token.Name.Attribute),
            (r':produce-unsat-assumptions', token.Name.Attribute),
            (r'!', token.Name.Attribute),
            (r'BitVec', token.Name.Attribute),
            (r'RNE', token.Name.Attribute),
            (r'Tuple', token.Name.Attribute),
            (r'true', token.String),
            (r'distinct', token.Operator),
            (r'=', token.Operator),
            (r'>', token.Operator),
            (r'and', token.Operator),
            (r'bvadd', token.Operator),
            (r'bvashr', token.Operator),
            (r'bvmul', token.Operator),
            (r'bvugt', token.Operator),
            (r'bvult', token.Operator),
            (r'bvule', token.Operator),
            (r'bvsdiv', token.Operator),
            (r'extract', token.Operator),
            (r'fp.gt', token.Operator),
            (r'ite', token.Operator),
            (r'mkTuple', token.Operator),
            (r'to_fp_unsigned', token.Operator),
            (r'\+zero', token.Operator),
            (r'#b[0-1]+', token.Text),
            (r'bv[0-9]+', token.Text),
            (r'".*?"', token.String),
            (r'[a-zA-Z][a-zA-Z0-9]*', token.Name),
            (r'[0-9]+', token.Number),
            (r'\s', token.Text),
            (r'\(_', token.Text),
            (r'\(', token.Text),
            (r'\)', token.Text),
            (r';.*$', token.Comment),
            (r'\.\.\.', token.Text)
        ]
    }


