#
# CSCI 384 Fall 2019
#
# eval: the evaluation component of the MiniML interpreter
#
# As part of Homework 07.
#
# This defines the evaluation components of a MiniML interpreter.  The
# key functions it defines are
#
#   eval(env,expn): evaluate expression term `expn` 
#                   within the name-value binding 
#                   context `env`. Gives back a 
#                   tagged value.
#
#   bind(env,defn): evaluate the RHS of a definition
#                   `defn` within the name-value 
#                   binding context `env`. Gives 
#                   back a context extended with
#                   that definition.
#
#                   This includes mutually recursive
#                   bindings of function names to a
#                   family of closures.
#
# The `expn` and `defn` terms are just ASTs produced by the parser. A
# name-value binding environment is just a list of string-value
# pairs. The values are "tagged values", namely a Python list
# typically of the form ["Type",value] where "Type" is one of "Unit",
# "Int", "Bool", "String", "List", "Product", "Closure", the standard
# types of MiniML, along with "Table" (for Homework 07) and "PrimFn"
# for representing built-in unary operations.  The `value` part is
# just our Python implementation of that MiniML value.
#
# There is support for pretty-printing values, using a function called
# `valueString`, and a function `namesOf` for inspecting a definition
# term for its names, i.e. its LHSs.
#

# ---

#
# Load the definition of `'a table` type's implementation.
#
from table import table

#
# Define the main error type raised by the interpreter.
#
class EvalError(Exception):
    pass

#
# PRIMITIVES
#
# This defines a dictionary of unary and binary operations so that
# they can be applied in the "eval" function.
#

PRIMITIVES = {}

# comparison
PRIMITIVES["<"] = (lambda a,b:   ["Bool", valueOf(a) < valueOf(b)]) 
PRIMITIVES["<="] = (lambda a,b:  ["Bool", valueOf(a) <= valueOf(b)]) 
PRIMITIVES[">"] = (lambda a,b:   ["Bool", valueOf(a) > valueOf(b)]) 
PRIMITIVES[">="] = (lambda a,b:  ["Bool", valueOf(a) >= valueOf(b)]) 

# equality
PRIMITIVES["="] = (lambda a,b:   ["Bool", valueOf(a) == valueOf(b)]) 
PRIMITIVES["<>"] = (lambda a,b:  ["Bool", valueOf(a) != valueOf(b)]) 

# ints
PRIMITIVES["+"] = (lambda a,b:   ["Int", valueOf(a) + valueOf(b)]) 
PRIMITIVES["-"] = (lambda a,b:   ["Int", valueOf(a) - valueOf(b)]) 
PRIMITIVES["div"] = (lambda a,b: ["Int", valueOf(a) // valueOf(b)]) 
PRIMITIVES["mod"] = (lambda a,b: ["Int", valueOf(a) % valueOf(b)]) 
PRIMITIVES["*"] = (lambda a,b:   ["Int", valueOf(a) * valueOf(b)]) 
PRIMITIVES["~"] = (lambda a:     ["Int", -valueOf(a)])

# bools (andalso and orelse are handled differently)
PRIMITIVES["not"] = (lambda a:   ["Bool", not valueOf(a)])

# strings and output
PRIMITIVES["^"] = (lambda a,b:   ["String", valueOf(a) + valueOf(b)]) 
PRIMITIVES["print"] = (lambda a: ["Unit", print(valueString(a))])
PRIMITIVES["makestring"] = (lambda a: ["String", valueString(a)])

# lists
PRIMITIVES["::"] = (lambda a,b:  ["List", [a] + valueOf(b)]) 
PRIMITIVES["@"] = (lambda a,b:   ["List", valueOf(a) + valueOf(b)])
PRIMITIVES["null"] = (lambda a:  ["Bool", len(valueOf(a)) == 0])
PRIMITIVES["hd"] = (lambda a:    (valueOf(a))[0])
PRIMITIVES["tl"] = (lambda a:    ["List", (valueOf(a))[1:]])

# pairs
PRIMITIVES[","] = (lambda a,b:   ["Product",(a,b)])
PRIMITIVES["fst"] = (lambda a:   (valueOf(a))[0])
PRIMITIVES["snd"] = (lambda a:   (valueOf(a))[1])

# tables
PRIMITIVES["?"] = (lambda a,b:   ["Bool",(valueOf(a)).contains(valueOf(b))])
PRIMITIVES["."] = (lambda a,b:   (valueOf(a)).lookUp(valueOf(b)))
PRIMITIVES["+:"] = (lambda a,b:  ["Table",(valueOf(a)).withAlso(valueOf(valueOf(b)[0]),valueOf(b)[1])])
PRIMITIVES["-:"] = (lambda a,b:  ["Table",(valueOf(a)).without(valueOf(b))])
PRIMITIVES["keys"] = (lambda a:  ["List",[["String",k] for k in (valueOf(a)).keys()]])
PRIMITIVES["size"] = (lambda a:  ["Int", (valueOf(a)).size()])

#
# MiniML value support
#
# Values are tagged and are represented in the form
#     [ tag , ... ]
# where 'tag' is "Unit", "Int", "Bool", "String", "List", "Product",
# "PrimFn", or "Closure".  Here ...  denotes the second component,
# which for all the values except "Closure" it is a Python value which
# holds the representation of the value itself.
# 
# For "Int", the representation is a Python integer.
# For "Bool", it is a Python boolean value, True or False.
# For "String", it is a Python string.
# For "Unit", the representation value is Python's 'None'.
# For the "List" type, it is a Python list of tagged values.
# For the "Product" type, it is a Python list of tagged values.
#
# The tag "PrimFn" denotes a built-in function e.g. for performing
# arithmetic or logic.  The value component is its MiniML identifier
# string.  See the dictionary called 'PRIMITIVES" above for what these
# are.
#
# The "Closure" value represents a function value. As a tagged value
# it is made up of several components.  The first is a string
# representing the function's parameter.  The second is an expression
# term (using our representation of ML abstract syntax terms from the
# parser) that represents the function's rule for evaluation.  The
# third is a variable-value binding environment, which ought to
# contain bindings for all the free variables in the function's rule
# that are not the function's parameter.  This environment is a
# capture of the lexically defined context in which the closure's
# definition was expressed.
#
# For a closure that is part of a collection of mutually defined
# recursive functions, the environment attached ultimately points back
# the function's closure, along with the closures of the other
# functions. This is so that the function will be able to call itself
# and those other functions.
#

def tagOf(tv):
    return tv[0]

def valueOf(tv):
    if tagOf(tv) == "Closure":
        return tv
    else:
        return tv[1]

def namesOf(defn):
    if defn[0] == "Val" or defn[0] == "Fun":
        return [defn[1]]
    else:
        return [d[1] for d in defn[1]]

#
# valueString
#
# Converts our MiniML value terms into Python strings.
#
def valueString(tv):
    t = tagOf(tv)
    v = valueOf(tv)
    if t == "Unit":
        return "()"
    elif t == "Int":
        return str(v)
    elif t == "Bool":
        if v:
            return "true"
        else:
            return "false"
    elif t == "String":
        return '"'+v+'"'
    elif t == "Table":
        s = '{'
        ks = v.keys()
        ss = [(k+"=>"+valueString(v.lookUp(k))) for k in ks]
        if len(ss) > 0:
            s += ss[0]
            for w in ss[1:]:
                s += ','
                s += w
        s += '}'
        return s
    elif t == "List":
        vs = v
        s = '['
        if len(vs) > 0:
            s += valueString(vs[0])
            for w in vs[1:]:
                s += ','
                s += valueString(w)
        s += ']'
        return s
    elif t == "Closure" or t == "PrimFn":
        return "fn"
    elif t == "Product":
        s1 = valueString(v[0])
        s2 = valueString(v[1])
        return "("+s1+","+s2+")"
    else:
        print(tv)
        raise EvalError("Unknown value to report.")



# THE MAIN INTERPRETER FUNCTIONS



#
# valueOfName(env,idn)
# 
# Gets the name bound within an environment, returns its associated
# value.
#
def valueOfName(env, idn):
    i = 0
    while i < len(env):
        if env[i][0] == idn:
            return env[i][1]
        i = i+1
    raise EvalError("Unbound name: '"+idn+"'.")

#
# bind
# 
# Add a name-value pair (or pairs) to `env` according to the given
# MiniML `defn` term. That value is determined within the context of
# `env`. Returns the environment extended by that (those)
# definition(s).
#
def bind(env,defn):

    # If it's a value definition, bind the name to
    # the expression's value.
    if defn[0] == "Val":
        x = defn[1]
        e = defn[2]
        v = eval(env,e)
        return [(x,v)]+env

    # If it's a function definition, bind its name to
    # a (recursive) closure.
    elif defn[0] == "Fun": 
        f = defn[1]
        x = defn[2]
        r = defn[3]
        v = ["Closure",x,r,None]
        C = [(f,v)]+env
        v[3] = C         # Make the closure 'recursive'
        return C

    # If it's several function definition, bind them as a 
    # collection of (mutually recursive) closures.
    elif defn[0] == "And":
        ds = defn[1]
        # Make a collection of mutually recursive function values. 
        vs = []
        # Build the extended context along the way.
        C = env
        for d in ds:
            # Make closures for each defined function.
            f = d[1]
            x = d[2]
            r = d[3]
            v = ["Closure",x,r,None] # Bogus closure, to be fixed later.
            vs = [v] + vs
            # Add a binding for each.
            C = [(f,v)] + C
        # Fix all the closures.
        for v in vs:
            v[3] = C     # Make each closure 'recursive'
        return C


#
# eval
# 
# Evaluate the MiniML `expn` term within the context `env`.
# Returns the resulting value.
#
def eval(env,expn):

    #
    # --------------
    # env |- () V ()
    #
    if expn[0] == "Unt":
        return ["Unit",None]

    #
    # ------------
    # env |- i V i
    #
    if expn[0] == "Num":
        i = expn[1]
        return ["Int",i]

    #
    # ------------
    # env |- b V b
    #
    if expn[0] == "Cnd":
        b = expn[1]
        return ["Bool",b]

    #
    # ------------
    # env |- s V s
    #
    if expn[0] == "Str":
        s = expn[1]
        return ["String",s]

    #
    # --------------
    # env |- pf V pf
    #
    if expn[0] == "Primitive":
        pf = expn[1]
        return ["PrimFn",pf]

    #
    # ---------------
    # env |- nil V []
    #
    if expn[0] == "Nil":
        return ["List",[]]

    #
    # -----------------
    # env |- empty V {}
    #
    if expn[0] == "Empty":
        return ["Table",table({})]

    #
    # -----------------
    # env |- x V env(x)
    #
    if expn[0] == "Var":
        x = expn[1]
        return valueOfName(env,x)

    # env |- c V true  env |- t V v
    # -----------------------------
    # env |- if c then t else e V v
    #
    # env |- c V false   env |- e V v
    # -------------------------------
    #  env |- if c then t else e V v
    #
    elif expn[0] == "If":
        c = expn[1]
        t = expn[2]
        e = expn[3]
        cv = eval(env,c)
        if valueOf(cv):
            return eval(env,t)
        else:
            return eval(env,e)

    #  
    # ----------------------------
    # env |- fn x => r V <x;r;env>
    #
    elif expn[0] == "Lam":
        x = expn[1]
        r = expn[2]
        return ["Closure",x,r,env]

    #
    # env |- e1 V <x;r;C>  env |- e2 V v2  [x->v2]C |- r V v
    # ------------------------------------------------------
    #                   env |- e1 e2 V v
    #
    elif expn[0] == "App":
        e1 = expn[1]
        e2 = expn[2]
        v1 = eval(env,e1)
        v2 = eval(env,e2)
        if tagOf(v1) == "PrimFn":
            op = valueOf(v1)
            rule = PRIMITIVES[op]
            try:
                v = rule(v2)
            except:
                msg = "Runtime error using primitive operation '%s' at %s"%(op,expn[-1])
                raise EvalError(msg)
            return v
        elif tagOf(v1) == "Closure":
            x = v1[1]
            r = v1[2]
            C = v1[3]
            v = eval([(x,v2)]+C,r)
            return v
        else:
            raise EvalError("Bad function application.")

    #
    # env |- e V v   [x->v]env |- b V w
    # ---------------------------------
    # env |- let val x = e in b end V w
    #           
    #         [f->v]env |- b V w
    # -----------------------------------
    # env |- let fun f x = r in b end V w
    #
    # where v satisfies <x;r;[f->v]env>.
    #           
    elif expn[0] == "Let":
        d = expn[1]
        b = expn[2]
        w = eval(bind(env,d),b)
        return w

    # env |- e1 V v1   env |- e2 V v2
    # -------------------------------
    #   env |- e1 op e2 V op(v1,v2)
    #           
    elif expn[0] == "Binop":
        op = expn[1]
        e1 = expn[2]
        e2 = expn[3]
        v1 = eval(env,e1)

        # Note: andalso and orelse are special forms.
        if op == "andalso":
            if valueOf(v1):
                return eval(env,e2)
            else:
                return v1
        if op == "orelse":
            if valueOf(v1):
                return v1
            else:
                return eval(env,e2)

        v2 = eval(env,e2)
        rule = PRIMITIVES[op]
        try:
            v = rule(v1,v2)
        except:
            msg = "Runtime error using primitive operation '%s' at %s"%(op,expn[-1])
            raise EvalError(msg)

        return v

