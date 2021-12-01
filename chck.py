#
# CSCI 384 Fall 2019
#
# The type system for MiniML.
#
# As part of Homework 07.
#
# BEGIN ASSIGNMENT
# ---
#
# The code is below is a *nearly* complete implementation of the type
# system for MiniML. Here is what is missing/unimplemented:
#
# * the `infer` code for checking the type of the list prepend
#   operation ::
#
# * the `infer` code for checking the type of the pair extraction
#   primitives fst/snd.
#
# * the `infer` code for checking the type of the list inspection
#   primitives null/hd/tl.
#
# ASSIGNMENT Part 1: make type checking work for each of these
# constructs.
#
# ---
#
# In addition, we've enhanced MiniML to include a dictionary type
# named "table."  Tables hold a collection of key-value pairs where
# the keys are strings and the pairs can be any MiniML value.  All the
# values in a table are required to be of the same type.
#
# For example, the type "int table" would be a dictionary whose
# entries associate a string with an integer value. Here are some
# examples of their use:
#
#    - val T = {hello=>4,bob=17};
#    val T = {hello=>4,bob=17} : int table
#    - T +: ("a",2);
#    val it = {hello=>4,bob=17,a=2} : int table
#    - empty +: ("goodbye",0);
#    val it = {goodbye=0} : int table
#    - T -: "hello";
#    val it = {bob=17} : int table
#    - T . "hello"
#    val it = 4 : int
#    - T ? "hello"
#    val it = true : bool
#    - size T;
#    val it = 2 : int
#    - keys T;
#    val it
#
# In the above, we're seeing several forms of syntax for building
# tables. Here in fact is the full suite of operations:
#
#    empty - an empty table, analogous to nil
#    +: - binary operation for extending a table with an entry
#    -: - binary operation for
#    ? - binary operation for key containment
#    . - binary operation for key lookup
#    size - primitive unary operation that gives the number of entries
#    keys - primitive unary operation that gives the list of keys
#
# ASSIGNMENT Part 2: write the rules for checking and inferring
# the type of these five table constructs. They shouldn't worry
# about polymorphism, just as we didn't when we wrote the rules
# for the contstructs relating to "Arrow", "List", "Int", "Product",
# "Bool", etc.
#
# ---
#
# In the code, these table constructs get parsed as these AST
# terms
#
#    ["Empty", p]
#    ["Binop", op, e1, e2, p] for op of "+:", "-:", "?", "."
#    ["Primitive", op] for op of "size", "keys"
#
# The typechecking function `infer`, however, does not handle
# these yet. The first should be handled in the part of the
# code that handles "Nil", the second should be handled in the
# part of the code that handles "Binop", and the last should be
# handled by the part of the code that handles "App" of a
# "Primitive".
#
# ASSIGNMENT Part 3a: write the pseudocode of INFER for each of
# these constructs, similar to what I provided in class.
#
# ASSIGNMENT Part 3b: modify `infer` in the code below so that
# it handles these constructs. Write a series of .mml file
# tests that demonstrate that it works.
#
# ---
# END ASSIGNMENT
#
# The documentation below here consists simply of comments describing
# the specifics of the implementation of the existing code. They
# probably do not need to be read for completing the assignment---
# several of the comments are mirrored in the PDF included in this
# repository---but they might be helpful for you while completing
# the assignment, or if you are just curious about how everything
# works.
#
# ---
#
# This code implements the components of the type system of the
# MiniML interpreter. The two key functions it defines are
#
#
#   1. tau := infer(tyc,expn)
#
#   This function takes a name-type context `tyc` and a MiniML term
#   `expn` and works to deduce a type `tau` for that expression.  It
#   does so by checking the subterms of the expression, making sure
#   the uses of names and language constructs within that expression
#   are consistent with the typing rules of the language. In doing so,
#   the algorithm relies on assumptions about the types of free names
#   within the expression. These assumptions are stored within the
#   type context `tyc`. This algorithm is what is given in the PDF
#   document included in this repository.
#
#
#   2. tyc' := check(tyc,defn)
#
#   This function is not much different than the above (I just needed
#   another name for a function). Rather than checking an expression,
#   it checks the "val" and "fun" constructs' definitions of
#   names. Rather than giving back the type of that name, or name(s),
#   we instead give those back as a modified context tyc'. Furthermore
#   the definitions are attached to a "let", and it is in `check` that
#   the type system intoduces a "forall type." This too is discussed
#   in the PDF document included in this repository.
#
#
# It should be noted that both functions wrestle with type variables
# in a number of ways. Oftentimes, during checking of an expression,
# the code has to invent a type of a name or a subexpression, but
# without yet knowing enough information about how that name is going
# to be used or not fully knowing what other expressions that
# subexpression might serve. Further checking the use of a name or
# the use of the result of a subexpression leads to constraints on
# their type. To do this, type variables are used, and an algorithm
# `unify` is used to resolve these contstraints. The code thus also
# defines
#
#
#    3. unify(tau1,tau2)
#
#    "Unifies" two type terms, ones that include type variables, by
#    seeking a set of substitutions of those variables with type
#    terms, so that `tau1` and `tau2` can be made equal. This
#    algorithm is laid out in the PDF document included in this
#    repository. The difference here from the pseudocode is that,
#    rather than returning a substitution, a "binding" is made to
#    the type variable object. In essence, the variable is no longer
#    free, but is instead replaced by that term everywhere it gets
#    used. The code raises a "mismatch error" should unification not
#    be possible.
#
#

class TypeError(Exception):
    pass

class TypeMismatch(Exception):
    pass

ORDEROP = ["<","<=",">",">="]
LOGICOP = ["andalso","orelse"]
EQUALOP = ["=","<>"]
ARITHOP = ["+","-","*","div","mod"]

#
# MiniML type support
#
# The code below is used for representing type terms that are
# judgements about the values of expressions in ML.  There are several
# kinds of types:
#
#    <type> ::= unit | bool | int | string
#    <type> ::= <type> list
#    <type> ::= <type> table
#    <type> ::= <type> -> <type>
#    <type> ::= <type> x <type>
#    <type> ::= 'a, 'b, 'c, ...
#
# The first of these are the 'ground' types.  The next three are
# recursive type terms.  The last of these are type variables.  These
# can appear in a type term in two ways:
#
#    1. within a polymorphic type
#
#    2. within a type term for an expression or name whose type has
#       not be pinned down by the system
#
# In the latter case, they serve as "named holes" in the term that can
# be filled with subterms.  In the former case, they serve as the
# "free" part of a type template that can be "instantiated" by the
# system.
#
# We use "tagged lists" to represent type term trees just as we did
# with ML expression terms.
#
# ["Unit"], ["Bool"], ["Int"], ["String"] are "leaf" terms
#
# and the rest are "internal node" terms of the form
#
#   ["List", tau ]
#   ["Table", tau ]
#   ["Arrow", tau1 , tau2 ]
#   ["Product", tau1 , tau2 ]
#

def kindOf(tau):
    assert(type(tau) == list and len(tau) >= 1)
    return tau[0]

def termsOf(tau):
    assert(kindOf(tau) != "TyVar" and type(tau) == list and len(tau) >= 1)
    return tau[1:]

def typeString(tau):
    if kindOf(tau) == "Unit":
        return "unit"
    elif kindOf(tau) == "Int":
        return "int"
    elif kindOf(tau) == "Bool":
        return "bool"
    elif kindOf(tau) == "String":
        return "string"
    elif kindOf(tau) == "List":
        s = "("+typeString(tau[1])+")"
        s += " list"
        return s
    elif kindOf(tau) == "Table":
        s = "("+typeString(tau[1])+")"
        s += " table"
        return s
    elif kindOf(tau) == "Arrow":
        s1 = "("+typeString(tau[1])+")"
        s2 = "("+typeString(tau[2])+")"
        return s1 + " -> " + s2
    elif kindOf(tau) == "Product":
        s1 = "("+typeString(tau[1])+")"
        s2 = "("+typeString(tau[2])+")"
        return s1 + " x " + s2
    elif kindOf(tau) == "TyVar":
        return tyVarName(tau)
    else:
        raise TypeError("Unknown type",tau,"to report.")


freshest = 0

def freshTyVar():
    global freshest
    name = "alpha_"+str(freshest)
    freshest = freshest + 1
    return ["TyVar",name,None]

def isTyVar(tau):
    return (kindOf(tau) == "TyVar")

def tyVarName(tyv):
    assert(isTyVar(tyv))
    return tyv[1]

def tyVarBinding(tyv):
    assert(isTyVar(tyv))
    return tyv[2]

def isFree(tau):
    return (isTyVar(tau) and tyVarBinding(tau) == None)

def bindTyVar(tyv,tau):
    assert(isFree(tyv))
    tyv[2] = tau

def tyVarsOf(tau):
    if kindOf(tau) == "Forall":
        return [v for v in tyVarsOf(tau[2]) if v not in tau[1]]
    elif isTyVar(tau):
        if isFree(tau):
            return [tyVarName(tau)]
        else:
            return tyVarsOf(tyVarBinding(tau))
    else:
        vs = []
        for sigma in termsOf(tau):
            vs += tyVarsOf(sigma)
        return vs

def tyVarsThroughout(tyc):
    vs = []
    for assump in tyc:
        (x,tau) = assump
        vs += tyVarsOf(tau)
    return vs

def sameTyVar(sigma,tau):
    assert(isFree(sigma))
    if isFree(tau):
        return tyVarName(sigma) == tyVarName(tau)
    else:
        taup = tyVarBinding(tau)
        if isVar(taup):
            return sameTyVar(sigma,taup)
        else:
            return False

def reportPlace(expn):
    return expn[-1]

def unifyBelow(sigma,tau):
    # We shouldn't be unifying any polymorphic type terms.
    assert(kindOf(sigma) != "Forall" and kindOf(tau) != "Forall")

    # Expand bound type variable terms.
    if isTyVar(sigma) and not isFree(sigma):
        unifyBelow(tyVarBinding(sigma),tau)
        return
    #
    if isTyVar(tau) and not isFree(tau):
        unifyBelow(sigma,tyVarBinding(tau))
        return

    # Bind a free variable term.
    if isTyVar(sigma):
        if isTyVar(tau) and tyVarName(sigma) == tyVarName(tau):
            return
        elif tyVarName(sigma) not in tyVarsOf(tau):
            bindTyVar(sigma,tau)
            return
        else:
            raise TypeMismatch("Circular binding attempted.")
    #
    if isTyVar(tau):
        if isTyVar(sigma) and tyVarName(sigma) == tyVarName(tau):
            return
        elif tyVarName(tau) not in tyVarsOf(sigma):
            bindTyVar(tau,sigma)
            return
        else:
            raise TypeMismatch("Circular binding attempted.")

    # Neither type term is a type variable.
    if kindOf(sigma) == kindOf(tau):
        sTerms = termsOf(sigma)
        tTerms = termsOf(tau)
        if len(sTerms) == len(tTerms):
            l = len(sTerms)
            for i in range(l):
                unifyBelow(sTerms[i],tTerms[i])
            return
        else:
            raise TypeMismatch("Different arity of type constructors.")
    else:
        raise TypeMismatch("Mismatch of type constructors.")


def expandTyVars(tau):
    if kindOf(tau) == "Forall":
        return ["Forall",tau[1],expandTyVars(tau[2])]
    elif isTyVar(tau):
        if isFree(tau):
            return tau
        else:
            return expandTyVars(tyVarBinding(tau))
    else:
        label = kindOf(tau)
        children = termsOf(tau)
        taup = [label]
        for c in children:
            taup = taup + [expandTyVars(c)]
        return taup

#
# unify(sigma,tau):
#
# Attempts to resolve the type term 'sigma' so that it matches the
# expected type term 'tau', binding any free type variable in either
# term to make the terms the same.
#
# Reports a type mismatch error if the attempt fails in some way.
#
# Relies on the helper 'unifyBelow' which is a recursive
# implementation of the UNIFY procedure.
#
def unify(sigma,tau):
    try:
        unifyBelow(sigma,tau)
    except TypeMismatch:
        message = "Type mismatch.\n"
        message += "Expected: "+typeString(expandTyVars(tau))+"\n"
        message += "Saw: "+typeString(expandTyVars(sigma))+"\n"
        raise TypeMismatch(message)
#
# subst(S,tau):
#
# Constructs a type term that is the same as 'tau', except
# with any free variables named in S replaced by its
# associated term in S
#
# Note that S represents a type variable substitution.  In
# class we wrote this as
#
#  S = [sigma1/alpha1, ... , sigmak/alphak]
#
# Here, S is a Python 'dict' that maps type variable names
# to type terms.  So we would instead have something like
#
#  S == {"alpha1":sigma1, ... , "alphak":sigma1}
#
def subst(S,tau):
    if isTyVar(tau):
        assert(isFree(tau))
        if tyVarName(tau) in S:
            return S[tyVarName(tau)]
        else:
            return tau
    else:
        label = kindOf(tau)
        children = termsOf(tau)
        taup = [label]
        for c in children:
            taup += [subst(S,c)]
        return taup

# tyVarNameFor(i):
#
# This constructs an alphabetic string, derived from the
# lexicographic index i.  That is, 0 gives back "'a", 1
# gives back "'b", 25 gives back "'z", 26 gives back "'aa",
# 27 gives back "'ab", and so on.
#
# These are used to generate readable type names for the
# polymorphic types reported by the REPL.
#
def tyVarNameFor(i):
    i += 0
    aTOz = [chr(97+j) for j in range(26)]
    s = "'"+aTOz[i%26]
    while i // 26 > 0:
        i //= 26
        s += aTOz[i%26]
    return s

# generalize(tyc,tau):
#
# This wraps up a type term 'tau' that has free type variables
# generated "from within", meaning they aren't free variables
# that appear in the assumptions of the type context 'tyc', as
# a polymorphic FORALL template term.
#
# If there are no such free variables, then the term is not
# wrapped with a FORALL, but rather is returned unchanged.
#
def generalize(tyc,tau):
    #
    # Determine the free type variables in tau that aren't in tyc.
    outside = tyVarsThroughout(tyc)
    within = tyVarsOf(tau)

    ws = []
    for w in within:
        if w not in ws and w not in outside:
            ws.append(w)

    #
    # I rewrote the above to make the readable alpha-renaming deterministic.
    # This is what it was before the rewrite:
    #
    #     ws = {w for w in within if w not in outside}
    #

    # See if there is any need to generalize 'tau' with a FORALL.
    n = len(ws)
    if n == 0:
        return tau

    # If so, rename them with more readable variable names.
    S = {}
    vs = []
    i = 0
    for w in ws:
        v = tyVarNameFor(i)
        S[w] = ["TyVar",v,None]
        vs = vs + [v]
        i = i + 1

    # Bind them all, wrapping the renamed term as a FORALL term.
    taup = expandTyVars(tau)
    sigma = ["Forall",vs,subst(S,taup)]
    return sigma


# instantiate(tau):
#
# This takes a FORALL polymorhic "template" term and replaces all
# its pattern variable names with fresh type variables.
#
def instantiate(tau):
    if kindOf(tau) == "Forall":

        # Get the binding pattern names.
        vs = tau[1]
        # Get the term that contains them.
        sigma = tau[2]

        # Now build a substitution list of fresh variables.
        S = {}
        for v in vs:
            S[v] = freshTyVar()

        # Give back a freshly instantiated term from the template 'tau'.
        return subst(S,sigma)

    else:
        # Not polymorphic, so no change.
        return tau

#
# type checking and inference
#


#
# tyc' := check(tyc,defn)
#
# This function checks the given VAL or FUN definition
# (or several FUN definitions in the case of AND) to
# determine the type of the name(s) being defined.
#
# If the type deduction is successful (through calls to
# the INFER procedure), it gives back a modified type
# context with a new type assumption (or assumptions)
# for the name(s) defined.
#
# Since ML uses "LET-bounded polymorphism", the type(s)
# returned are "generalized" into a FORALL template
# type term, when appropriate.  See 'generalize' for
# details.
#
def check(tyc,defn):
    if defn[0] == "Val":
        #
        # G |- e : s   [x:gen(s)]G |- b : t
        # ---------------------------------
        #  G |- let val x = e in b end : t
        #
        x = defn[1]
        e = defn[2]
        sigma = infer(tyc,e)
        return [(x,generalize(tyc,sigma))]+tyc

    elif defn[0] == "Fun":
        #
        # [f:t1->t2,x:t1]G |- r : t2   [f:gen(G,t1->t2)]G |- b : t
        # --------------------------------------------------------
        #             G |- let fun f x = r in b end : t
        #
        f = defn[1]
        x = defn[2]
        r = defn[3]
        alpha = freshTyVar()
        beta = freshTyVar()
        sigma = ["Arrow",alpha,beta]
        rho = infer([(x,alpha),(f,sigma)]+tyc,r)
        unify(beta,rho)
        return [(f,generalize(tyc,sigma))]+tyc

    elif defn[0] == "And":
        # Check a collection of mutually recursive function definitions.
        ds = defn[1]
        fs = [defn[1] for defn in ds]
        xtypes = {f:freshTyVar() for f in fs}
        rtypes = {f:freshTyVar() for f in fs}
        ftypes = {f:["Arrow",xtypes[f],rtypes[f]] for f in fs}
        tycp = [(f,ftypes[f]) for f in fs]
        for d in ds:
            f = d[1]
            x = d[2]
            r = d[3]
            rho = infer([(x,xtypes[f])]+tycp+tyc,r)
            unify(rtypes[f],rho)
        tycp = [(f,generalize(tyc,ftypes[f])) for f in fs]
        return tycp+tyc

    else:
        raise TypeError("Weird definition term.")

# typeOfName(tyc,idn)
#
# Performs a type context "look up" to determine the
# type term assumed for the name 'idn'.
#
def typeOfName(tyc,idn):
    for a in tyc:
        (y,tau) = a
        if idn==y:
            return tau
    raise TypeError("Variable's type not found in the type context.")

#
# tau := infer(tyc,expn)
#
# Performs the Hindley-Milner algorithm for type checking and type
# inference.  This provides a (potentially polymorhic) type term
# describing the value expected to result from evaluation of the given
# ML term 'expn'.
#
# The code is an implementation of the typing deduction rules we
# devised in class, where type expectations are enforced by building
# type term "templates", using type variable subterms to defer pinning
# down portions of the type term, keeping them as general as the
# structure of the expression allows.  When the expression dictates
# constraints on the types of subterms, we use the helper UNIFY
# procedure to "pin down" (or bind) type variable subterms when we
# can.
#
# Should any type constraints be unresolvable, through a FAILURE of
# the UNIFY procedure, we raise a meaningful type mismatch error
# indicating the place in the source code where the mismatch occurs.
#
def infer(tyc,expn):
    try:
        if expn[0] == "Binop":
            op = expn[1]
            e1 = expn[2]
            e2 = expn[3]
            tau1 = infer(tyc,e1)
            tau2 = infer(tyc,e2)
            if op in ARITHOP:
                #
                # G |- e1 : int  G |- e2 : int
                # ----------------------------
                #     G |- e1 iop e2 : int
                #
                unify(tau1,["Int"])
                unify(tau2,["Int"])
                return ["Int"]

            elif op in LOGICOP:
                #
                # G |- e1 : bool  G |- e2 : bool
                # ------------------------------
                #      G |- e1 lgc e2 :bool
                #
                unify(tau1,["Bool"])
                unify(tau2,["Bool"])
                return ["Bool"]

            elif op in ORDEROP:
                #
                # G |- e1 : int  G |- e2 : int
                # ----------------------------
                #    G |- e1 cmp e2 : bool
                #
                unify(tau1,["Int"])
                unify(tau2,["Int"])
                return ["Bool"]

            elif op in EQUALOP:
                #
                # G |- e1 : t   G |- e2 : t
                # -------------------------
                #   G |- e1 cmp e2 : bool
                #
                unify(tau2,tau1)
                return ["Bool"]

            elif op == "::":
                #
                # G |- e1 : t1    G |- e2 : list t1
                # ---------------------------------
                #      G |- e1 :: e2 : list t1
                #
                unify(["List", tau1], tau2)
                return tau2

            elif op == "@":
                #
                # G |- e1 : s list   G |- e2 : s list
                # -----------------------------------
                #        G |- e1 @ e2 : list s
                #
                unify(tau1,tau2)
                alpha = freshTyVar()
                unify(tau1,["List",alpha])
                return tau1

            elif op == "+:":
                # create a new entry
                alpha = freshTyVar()
                unify(tau1, ["Table", alpha])
                unify(tau2, ["Product", ["String"], alpha])  # where alpha is the type given for the new entry
                return tau1

            elif op == "-:":
                # remove an entry
                alpha = freshTyVar()
                unify(tau1, ["Table", alpha])
                unify(tau2, ["String"])
                return tau1

            elif op == ".":
                # get the value at some key
                alpha = freshTyVar()
                unify(tau1, ["Table", alpha])  # for e1.e2, e1 is a table of any type
                unify(tau2, ["String"])  # and e2 is a key
                return alpha  # return the type of the table contents

            elif op == "?":
                # check if a key exists
                alpha = freshTyVar()
                unify(tau1, ["Table", alpha])  # for e1?e2, e1 is a table of any type
                unify(tau2, ["String"])  # and e2 is a key
                return ["Bool"]

            elif op == ",":
                #
                # G |- e1 : t1    G |- e2 : t2
                # ----------------------------
                #    G |- (e1,e2) : t1 x t2
                #
                return ["Product",tau1,tau2]

            elif op == "^":
                #
                # G |- e1 : string   G |- e2 : string
                # -----------------------------------
                #        G |- e1 ^ e2 : string
                #
                unify(tau1,["String"])
                unify(tau2,["String"])
                return ["String"]

            else:
                raise TypeError("Unrecognized binary operation.",e)

        elif expn[0] == "App" and expn[1][0] == "Primitive":
            op = expn[1][1]
            a = expn[2]
            tau = infer(tyc,a)
            if op == "~":
                #
                #  G |- a : int
                # --------------
                # G |- ~ a : int
                #
                unify(tau,["Int"])
                return ["Int"]

            elif op == "not":
                #
                #   G |- a : int
                # ----------------
                # G |- not a : int
                #
                unify(tau,["Bool"])
                return ["Bool"]

            elif op == "null":
                #
                #  G |- a : list t
                # ------------------
                # G |- null a : bool
                #
                alpha = freshTyVar()
                unify(tau, ["List", alpha])
                return ["Bool"]

            elif op == "hd":
                #
                # G |- a : t list
                # ---------------
                #  G |- hd a : t
                #
                alpha = freshTyVar()
                unify(tau, ["List", alpha])
                return alpha

            elif op == "tl":
                #
                #  G |- a : t list
                # ------------------
                # G |- tl a : t list
                #
                alpha = freshTyVar()
                unify(tau, ["List", alpha])
                return tau

            elif op == "fst":
                #
                # G |- a : t1 x t2
                # ----------------
                #  G |- fst a : t1
                #
                alpha = freshTyVar()
                unify(tau, ["Product", alpha, alpha])
                return alpha

            elif op == "snd":
                #
                # G |- a : t1 x t2
                # ----------------
                #  G |- snd a : t2
                #
                alpha = freshTyVar()
                unify(tau, ["Product", alpha, alpha])
                return alpha

            elif op == "size":
                # number of entries in a table
                alpha = freshTyVar()
                unify(tau, ["Table", alpha])
                return ["Int"]

            elif op == "keys":
                # list of keys in a table
                alpha = freshTyVar()
                unify(tau, ["Table", alpha])
                return ["List", ["String"]]  # list of keys is a list of strings

            elif op == "print":
                #
                #     G |- a : t
                # -------------------
                # G |- print a : unit
                #
                return ["Unit"]

            elif op == "makestring":
                #
                #         G |- a : t
                # --------------------------
                # G |- makestring a : string
                #
                return ["String"]

            else:
                raise TypeError("Unrecognized unary operation.",expn)

        elif expn[0] == "If":
            #
            # G |- c : bool  G |- e1 : t1  G |- e2 : t1
            # -----------------------------------------
            #       G |- if c then t else e : t1
            #
            c = expn[1]
            t = expn[2]
            e = expn[3]
            tau = infer(tyc,c)
            tau1 = infer(tyc,t)
            tau2 = infer(tyc,e)
            unify(tau,["Bool"])
            unify(tau2,tau1)
            return tau1

        elif expn[0] == "Unt":
            return ["Unit"]

        elif expn[0] == "Cnd":
            return ["Bool"]

        elif expn[0] == "Num":
            return ["Int"]

        elif expn[0] == "Str":
            return ["String"]

        elif expn[0] == "Nil":
            # Special case for nil.
            alpha = freshTyVar()
            return ["List",alpha]

        elif expn[0] == "Empty":
            # Special case for empty.
            alpha = freshTyVar()
            return ["Table", alpha]

        elif expn[0] == "Var":
            #
            # -----------------------
            # G |- x : instance(G(x))
            #
            tau = typeOfName(tyc, expn[1])
            if tau == None:
                raise TypeError((reportPlace(expn)+": Unbound identifier '%s'.") % expn[1])
            taup = instantiate(tau)
            return taup

        elif expn[0] == "Let":
            #
            # see check for the inference rules
            #
            d = expn[1]
            b = expn[2]
            tau = infer(check(tyc,d),b)
            return tau

        elif expn[0] == "App":
            #
            # G |- e1 : t2->s  G |- e2 : t2
            # -----------------------------
            #       G |- e1 e2 : s
            #
            e1 = expn[1]
            e2 = expn[2]
            tau1 = infer(tyc,e1)
            tau2 = infer(tyc,e2)
            beta = freshTyVar()
            tau = ["Arrow",tau2,beta]
            unify(tau1,tau)
            return beta

        elif expn[0] == "Lam":
            #
            #     [x:s]G |- r : t
            # -----------------------
            # G |- fn x => r : s -> t
            #
            x = expn[1]
            r = expn[2]
            alpha = freshTyVar()
            tau = infer([(x,alpha)]+tyc,r)
            return ["Arrow",alpha,tau]

        else:
            raise TypeError("Unknown expression term "+str(expn)+".")

    except TypeMismatch as tm:
        raise TypeError(reportPlace(expn)+": "+ tm.args[0])

# topLevelType(typ)
#
# This gives back a type term that can be reported at the "front end"
# of a MiniML interpreter. This means that "forall" types are only
# expressed implicitly, as terms with type variables.
#
def topLevelType(typ):
    if kindOf(typ) == "Forall":
        typ = typ[2]
    return expandTyVars(typ)
