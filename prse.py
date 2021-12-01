class LexError(Exception):
    pass

class SyntaxError(Exception):
    pass

# 
# Keywords, primitives, unary operations, and binary operations.
#
# The code below defines several strings or string lists used by
# the lexical analyzer (housed as class TokenStream, below).
#

RESERVED = ['if','then','else',
            'fn',
            'let','val','fun','and','in','end',
            'case','of','lft','rgt',
            'andalso','orelse',
            'div','mod',
            'eof']

UNOPS = ['~','not',
         'print','makestring',
         'hd','tl','null',
         'fst','snd','lft','rgt',
         'size','keys']

LITERALS = ['true','false',   
            'nil',
            'empty']

DELIMITERS = '()[]{},;'

# Characters that make up UN/BINOPS
OPERATORS = '~<>=*+-:^@?.|' 
    

#
# BINOPS
#
# This defines a precedence hierarchy of binary operations, ordered
# from lowest to highest precedence, with equal-precedence operators
# held at the same entry.  At each precedence level, we tag them as
# being either left- or right-associative.  This table is used to 
# guide the "parseInfix" function defined further below.
#
LEFT_ASSOC = 0
RGHT_ASSOC = 1
NONE_ASSOC = 2
BINOPS_LEVELS = 10
BINOPS    = [ None for i in range(BINOPS_LEVELS) ]
BINOPS[0] = (["orelse"],LEFT_ASSOC)
BINOPS[1] = (["andalso"],LEFT_ASSOC)
BINOPS[2] = (["=","<>","<",">","<=",">="],LEFT_ASSOC)
BINOPS[3] = (["@"],LEFT_ASSOC)
BINOPS[4] = (["::"],RGHT_ASSOC)
BINOPS[5] = (["+:","-:"],LEFT_ASSOC)
BINOPS[6] = (["?"],NONE_ASSOC)
BINOPS[7] = (["."],LEFT_ASSOC)
BINOPS[8] = (["+","-","^"],LEFT_ASSOC)
BINOPS[9] = (["*","div","mod"],LEFT_ASSOC)

INFIX = []
for level in range(BINOPS_LEVELS):
    INFIX += BINOPS[level][0]

def assoc(level):
    return BINOPS[level][1]

def binops(level):
    return BINOPS[level][0]

#
# LEXICAL ANALYSIS / TOKENIZER
#
# The code below converts ML source code text into a sequence 
# of tokens (a list of strings).  It does so by defining the
#
#    class TokenStream
#
# which describes the methods of an object that supports this
# lexical conversion.  The key method is "analyze" which provides
# the conversion.  It is the lexical analyzer for ML source code.
#
# The lexical analyzer works by CHOMP methods that processes the
# individual characters of the source code's string, packaging
# them into a list of token strings.
#
# The class also provides a series of methods that can be used
# to consume (or EAT) the tokens of the token stream.  These are
# used by the parser.
#


class TokenStream:

    def __init__(self,src,filename="STDIN"):
        """
        Builds a new TokenStream object from a source code string.
        """
        self.sourcename = filename
        self.source = src # The char sequence that gets 'chomped' by the lexical analyzer.
        self.tokens = []  # The list of tokens constructed by the lexical analyzer.
        self.extents = []     
        self.starts = []

        # Sets up and then runs the lexical analyzer.
        self.initIssue()
        self.analyze()
        self.tokens.append("eof")

    #
    # PARSING helper functions
    #

    def lexassert(self,c):
        if not c:
            self.raiseLex("Unrecognized character.")

    def raiseLex(self,msg):
        s = self.sourcename + " line "+str(self.line)+" column "+str(self.column)
        s += ": " + msg
        raise LexError(s)

    def next(self):
        """
        Returns the unchomped token at the front of the stream of tokens.
        """
        return self.tokens[0]

    def advance(self):
        """ 
        Advances the token stream to the next token, giving back the
        one at the front.
        """
        tk = self.next()
        del self.tokens[0]
        del self.starts[0]
        return tk

    def report(self):
        """ 
        Helper function used to report the location of errors in the 
        source code.
        """
        lnum = self.starts[0][0]
        cnum = self.starts[0][1]
        return self.sourcename + " line "+str(lnum)+" column "+str(cnum)

    def eat(self,tk):
        """
        Eats a specified token, making sure that it is the next token
        in the stream.
        """
        if tk == self.next():
            return self.advance()
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected: '"+tk+"'. "
            raise SyntaxError(err1 + err2 + err3)

    def eatInt(self):
        """
        Eats an integer literal token, making sure that such a token is next
        in the stream.
        """
        if self.nextIsInt():
            tk = self.advance()
            if tk[0] == '~':
                return -int(tk[1:])
            else:
                return int(tk)
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected an integer literal. "
            raise SyntaxError(err1 + err2 + err3)

    def eatName(self):
        """
        Eats a name token, making sure that such a token is next in the stream.
        """
        if self.nextIsName():
            return self.advance()
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected a name. "
            raise SyntaxError(err1 + err2 + err3)

    def eatString(self):
        """
        Eats a string literal token, making sure that such a token is next in the stream.
        """
        if self.nextIsString():
            return self.advance()[1:-1]
        else:
            where = self.report()
            err1 = "Unexpected token at "+where+". "
            err2 = "Saw: '"+self.next()+"'. "
            err3 = "Expected a string literal. "
            raise SyntaxError(err1 + err2 + err3)

    def nextIsInt(self):
        """
        Checks if next token is an integer literal token.
        """
        tk = self.next()
        return tk.isdigit() or (tk[0] == '~' and tk[1:].isdigit())

    def nextIsName(self):
        """
        Checks if next token is a name.
        """
        tk = self.next()
        isname = tk[0].isalpha() or tk[0] =='_'
        for c in tk[1:]:
            isname = isname and (c.isalnum() or c == '_')
        return isname and (tk not in RESERVED)

    def nextIsString(self):
        """
        Checks if next token is a string literal.
        """
        tk = self.next()
        return tk[0] == '"' and tk[-1] == '"'

    #
    # TOKENIZER helper functions
    #
    # These are used by the 'analysis' method defined below them.
    #
    # The parsing functions EAT the token stream, whereas
    # the lexcial analysis functions CHOMP the source text
    # and ISSUE the individual tokens that form the stream.
    #

    def initIssue(self):
        self.line = 1
        self.column = 1
        self.markIssue()

    def markIssue(self):
        self.mark = (self.line,self.column)

    def issue(self,token):
        self.tokens.append(token)
        self.starts.append(self.mark)
        self.markIssue()

    def nxt(self,lookahead=1):
        if len(self.source) == 0:
            return ''
        else:
            return self.source[lookahead-1]

    def chompWord(self):
        self.lexassert(self.nxt().isalpha() or self.nxt() == '_')
        token = self.chompChar()
        while self.nxt().isalnum() or self.nxt() == '_':
            token += self.chompChar()
        self.issue(token)
        
    def chompInt(self):
        self.lexassert(self.nxt().isdigit())
        token = ""
        token += self.chompChar()     # first digit
        while self.nxt().isdigit():
            token += self.chompChar() # remaining digits=
        self.issue(token)
        
    def chompString(self):
        self.lexassert(self.nxt() == '"')
        self.chompChar() # eat quote
        token = ""
        while self.nxt() != '' and self.nxt() != '"':
            if self.nxt() == '\\':
                self.chompChar()
                if self.nxt() == '\n':
                    self.chompWhitespace(True)
                elif self.nxt() == '\\':
                    token += self.chompChar()
                elif self.nxt() == 'n':
                    self.chompChar()
                    token += '\n'
                elif self.nxt() == 't':
                    self.chompChar()
                    token += '\t'
                elif self.nxt() == '"': 
                    self.chompChar()
                    token += '"'
                else:
                    self.raiseLex("Bad string escape character")
            elif self.nxt() == '\n':
                self.raiseLex("End of line encountered within string")
            elif self.nxt() == '\t':
                self.raiseLex("Tab encountered within string")
            else:
                token += self.chompChar()

        if self.nxt() == '':
            self.raiseLex("EOF encountered within string")
        else:
            self.chompChar() # eat endquote
            self.issue('"'+token+'"')

    def chompComment(self):
        self.lexassert(len(self.source)>1 and self.source[0:2] == '(*')
        self.chompChar() # eat (*
        self.chompChar() #
        while len(self.source) >= 2 and self.source[0:2] != '*)':        
            self.chomp()
        if len(self.source) < 2:
            self.raiseLex("EOF encountered within comment")
        else:
            self.chompChar() # eat *)
            self.chompChar() #     

    def chomp(self):
        if self.nxt() in "\n\t\r ":
            self.chompWhitespace()
        else:
            self.chompChar()

    def chompChar(self):
        self.lexassert(len(self.source) > 0)
        c = self.source[0]
        self.source = self.source[1:]
        self.column += 1
        return c

    def chompWhitespace(self,withinToken=False):
        self.lexassert(len(self.source) > 0)
        c = self.source[0]
        self.source = self.source[1:]
        if c == ' ':
            self.column += 1
        elif c == '\t':
            self.column += 4
        elif c == '\n':
            self.line += 1
            self.column = 1
        if not withinToken:
            self.markIssue()
        
    def chompOperator(self):
        token = ''
        while self.nxt() in OPERATORS:
            token += self.chompChar()
        self.issue(token)

    #
    # TOKENIZER
    #
    # This method defines the main loop of the
    # lexical analysis algorithm, one that converts
    # the source text into a list of token strings.

    def analyze(self):
        while self.source != '':
            # CHOMP a string literal
            if self.source[0] == '"':
                self.chompString()
            # CHOMP a comment
            elif self.source[0:2] == '(*':
                self.chompComment()
            # CHOMP whitespace
            elif self.source[0] in ' \t\n\r':
                self.chompWhitespace()
            # CHOMP an integer literal
            elif self.source[0].isdigit():
                self.chompInt()
            # CHOMP a single "delimiter" character
            elif self.source[0] in DELIMITERS:
                self.issue(self.chompChar())
            # CHOMP an operator               
            elif self.source[0] in OPERATORS:
                self.chompOperator()
            # CHOMP a reserved word or a name.
            else:
                self.chompWord()

#
# PARSER
#
#

def parseExpn(tokens):
    e = parseIfFn(tokens)
    return e

def parseIfFn(tokens):

    if tokens.next() == "if":
        #
        # <expn> ::= if <expn> then <expn> else <expn>
        #
        place = tokens.report()
        tokens.eat("if")
        c = parseExpn(tokens)
        tokens.eat("then")
        t = parseExpn(tokens)
        tokens.eat("else")
        e = parseExpn(tokens)
        return ["If",c,t,e,place]
  
    elif tokens.next() == "fn":
        #
        # <expn> ::= fn <name> => <expn>
        #
        place = tokens.report()
        tokens.eat("fn")
        x = tokens.eatName()
        tokens.eat("=>")
        e = parseExpn(tokens)
        return ["Lam",x,e,place]

    else:
        return parseInfix(tokens,0)

def parseInfix(tokens,level=0):

    #
    # Check if we should stop parsing INFIX expressions.
    #
    if level >= BINOPS_LEVELS:
        return parseApply(tokens)

    #
    # Parse the first expression. See if a BINOP follows.
    #
    first = parseInfix(tokens,level+1)
    if tokens.next() not in binops(level):
        # There is no BINOP at this precedence level.
        return first

    #
    # If there is a BINOP at this precedence level, consume it 
    # and then parse the righthand expression.
    #
    # <expn> ::= <expn> op <expn> ...? 
    #
    p = tokens.report()
    tk = tokens.advance()                # Consumes the BINOP.
    second = parseInfix(tokens,level+1)  # Parses the RHS.

    #
    # Parse the remaining "op <expn> op <expn> ... op <expn>", if
    # there are more.
    # 
    # Build a list of those remaining expressions, along with the
    # connnexting tokens.
    #
    es = [second]
    ts = [tk]
    ps = [p]
    while tokens.next() in binops(level):
        ps = ps + [tokens.report()]
        tk = tokens.advance()
        ts.append(tk)
        e = parseInfix(tokens,level+1)
        es.append(e)

    # Stitch together the subexpressions into a binary 
    # laid out according to the operators' associativity.
    #
    if assoc(level) == LEFT_ASSOC:
        t = first
        for i in range(len(es)):
            t = ["Binop",ts[i],t,es[i],ps[i]]
        return t
    else:
        es = [first] + es
        t = es.pop()
        while es != []:
            t = ["Binop",ts.pop(),es.pop(),t,ps.pop()]
        return t

STOPPERS = [",","end",")","]","}","val","fun","and","in","then","else","eof"]
STOPPERS = STOPPERS + INFIX

def parseApply(tokens):
    #
    # <expn> ::= <expn> <expn>
    #
    t = parseAtom(tokens)
    while not(tokens.next() in STOPPERS):
        place= tokens.report()
        e = parseAtom(tokens)
        t = ["App",t,e,place]
    return t

def nestLets(ds,b,p):
    e = b
    while len(ds) > 0:
        d = ds[-1]
        ds = ds[:-1]
        e = ["Let",d,e,p]
    return e

def parseAtom(tokens):
    #
    # <expn> ::= 375
    #
    if tokens.nextIsInt():
        place = tokens.report()
        return ["Num",tokens.eatInt(),place]

    #
    # <expn> ::= "hello, world."
    #
    elif tokens.nextIsString():
        place = tokens.report()
        return ["Str",tokens.eatString(),place]

    #
    # <expn> ::= () | ( <expn>,<expn> ) | ( <expn> )
    #
    elif tokens.next() == '(':
        place = tokens.report()
        tokens.eat('(')
        if tokens.next() == ')':
            # parse a Unit
            e = ["Unt",place]
        else:
            e = parseExpn(tokens)
            if tokens.next() == ',':
                # parse a Pair
                place = tokens.report()
                tokens.eat(',')
                e = ["Binop",",",e,parseExpn(tokens),place]
        tokens.eat(')')
        return e
    #
    # <expn> ::= [] | [ <expn> ] | [ <expn>, ... ,<expn> ] 
    #
    elif tokens.next() == '[':
        # parse a list
        tokens.eat('[')
        place = tokens.report()
        elts = []
        if tokens.next() != ']':
            # Parsing a list of length one or more.
            # Build a list of the list's expressions.
            elts += [(parseExpn(tokens), tokens.report())]
            while tokens.next() == ',':
                # Parse the next list element.
                tokens.eat(',')
                elts += [(parseExpn(tokens), tokens.report())]
        tokens.eat(']')

        # Build a "Cons" tree.
        el = ["Nil",place]
        while len(elts) > 0:
            e,p = elts.pop()
            el = ["Binop","::",e,el,p]

        return el
    #
    # <expn> ::= {} | { <id>=><expn> } | { <id>=><expn>, ... , <id>=><expn> }
    #
    elif tokens.next() == '{':
        # parse a table
        tokens.eat('{')
        place = tokens.report()
        et = ["Empty",place]
        if tokens.next() != '}':
            # Parsing a table of size one or more.
            place = tokens.report()
            x = tokens.eatName()
            tokens.eat("=>")
            placea = tokens.report()
            v = parseExpn(tokens)
            e = ["Binop",",",["Str",x,place],v,placea]
            et = ["Binop","+:",et,e,place]
            while tokens.next() == ',':
                # Parse the next list element.
                place = tokens.report()
                tokens.eat(',')
                placex = tokens.report()
                x = tokens.eatName()
                tokens.eat("=>")
                placea = tokens.report()
                v = parseExpn(tokens)
                e = ["Binop",",",["Str",x,placex],v,placea]
                et = ["Binop","+:",et,e,place]
        tokens.eat('}')
        return et
    #
    # <expn> ::= let <defns> in <expn> end
    #
    elif tokens.next() == "let":
        # Parse the full expression.
        place = tokens.report()
        tokens.eat("let")
        ds = parseDefns(tokens) # Read a set of definitions.
        tokens.eat("in")
        b = parseExpn(tokens)
        tokens.eat("end")
        # Build a series of nested LETs, one for each definition.
        return nestLets(ds,b,place)

    #
    # <expn> ::= true | false
    #
    elif tokens.next() in ["true","false"]:
        place = tokens.report()
        b = tokens.advance()
        if b == "true":
            return ["Cnd",True,place]
        else:
            return ["Cnd",False,place]

    #
    # <expn> ::= nil
    #
    elif tokens.next() == "nil":
        place = tokens.report()
        tokens.advance()
        return ["Nil",place]

    #
    # <expn> ::= empty
    #
    elif tokens.next() == "empty":
        place = tokens.report()
        tokens.advance()
        return ["Empty",place]

    #
    # <expn> ::= <primitive unary operation>
    #
    elif tokens.next() in UNOPS:
        place = tokens.report()
        unop = tokens.advance()
        return ["Primitive",unop,place]

    #
    # <expn> ::= <name>
    #
    elif tokens.nextIsName():
        place = tokens.report()
        x = tokens.eatName()
        return ["Var",x,place]

    else:
        where = tokens.report()
        err1 = "Unexpected token at "+where+". "
        err2 = "Saw: '"+tokens.next()+"'. "
        raise SyntaxError(err1 + err2)

def parseDefn(tokens):

    #
    # <defn> ::= val <name> = <expn>
    #
    if tokens.next() == "val":
        #
        place = tokens.report()
        tokens.eat("val")
        x = tokens.eatName()
        tokens.eat("=")
        e = parseExpn(tokens)
        return ["Val",x,e,place]

    #
    # <defn> ::= fun <fdef> and <fdef> and ... and <fdef> 
    # <fdef> ::= <name> ... <name> = <expn> 
    #
    elif tokens.next() == "fun":
        #
        place = tokens.report()        
        tokens.eat("fun")
        ds = []
        keepGoing = True
        while keepGoing: 
            f = tokens.eatName() # Function name.
            x = tokens.eatName() # First formal parameter.

            # Read any remaining formal parameters.
            xs = []
            while tokens.nextIsName():
                xs.append(tokens.eatName())

            tokens.eat("=")
            e = parseExpn(tokens) # Function evaluation rule.

            # Curry the remaining formal parameters.
            while len(xs) > 0:
                e = ["Lam",xs.pop(),e]

            # Build the function term.
            fdef = ["Fun",f,x,e,place]
            ds += [fdef]

            if tokens.next() == "and":
                tokens.eat("and")
            else:
                keepGoing = False

        # See if there was mutual recursion.
        if len(ds) > 1:
            return ["And",ds]
        else:
            return ds[0]

    else:
        where = tokens.report()
        err1 = "Unexpected 'val' or 'fun' at "+where+". "
        err2 = "Saw: '"+tokens.next()+"'. "
        raise SyntaxError(err1 + err2)

def parseDefns(tokens):
    #
    # <defns> ::= <defn> ... <defn>
    #
    ds = []
    while tokens.next() in ["val","fun"]:
        ds.append(parseDefn(tokens))
    return ds

def parseFile(fname):
    f = open(fname,"r")
    src = f.read()
    tks = TokenStream(src,filename=fname)
    return parseDefns(tks)

def parseEntry(ent):
    tks = TokenStream(ent)
    # If it is a definition
    if tks.next() in ["val","fun"]:
        dfn = parseDefn(tks)
    else:
        dfn = ["Val","it",parseExpn(tks)]
    return dfn
