#
# CSCI 384 Fall 2021
#
# the MiniML interpreter, with Hindley-Milner type checking and inference.
#
# As part of Homework 07.
#
# This is the top-level interactive component of a MiniML interpreter.
# It parses, type checks, and then evaluates expressions written in 
# the MiniML programming language.
#
# It relies on the Python modules:
#
#   prse.py: the parser for MiniML programs and expressions 
#   eval.py: the evaluator of MiniML expression and definition terms
#   chck.py: the type checker and inference engine for MiniML
#
# It can be run as follows:
#
#    python3 miniml.py <file1> <file2> ... <filek>
#
# where each <filei> is the name of a .mml source file, though no
# files need to be listed.
#
# It loads the defintions given in any such files, one at a time, and
# then allows the programmer to interact with the system, either by
# entering more definitions (with "fun" and "val"), or by entering
# MiniML expressions. In the latter case, the expression is evaluated
# and its value and type are reported.
#

import sys

from prse import parseEntry, parseFile, LexError, SyntaxError
from chck import typeOfName, check, topLevelType, typeString, TypeError
from eval import valueOfName, bind, namesOf, valueString, EvalError

#
# reply
#
# Reports the name-value-type of a new binding.
#
def reply(idn,vlu,typ):
    print("val "+idn+" = "+valueString(vlu)+" : "+typeString(topLevelType(typ)))

#
# topBind
#
# Adds a new bound name (or names) to the value and type contexts
# `env` and `tyc` as a result of evaluating the given `dfn`.
#
# Reports that new binding (or bindings).
#
# Returns the two contexts, extended by that definition.
#
def topBind(env,tyc,dfn):
    try:
        xs = namesOf(dfn)
        tycp = check(tyc,dfn)
        envp = bind(env,dfn)
        for x in xs:
            vlu = valueOfName(envp,x)
            tau = typeOfName(tycp,x)
            reply(x,vlu,tau)
        return (envp,tycp)
    except TypeError as te:
        print(te.args[0])
        return (env,tyc)
    except EvalError as ee:
        print(ee.args[0])
        return (env,tyc)

#
# topBindAll
#
# Adds a collection of new bound name (or names) to the value and type
# contexts `env` and `tyc` as a result of evaluating the given list of
# definitions. Returns those two extended contexts.
#
def topBindAll(env,tyc,dfns):
    for dfn in dfns:
        (env,tyc) = topBind(env,tyc,dfn)
    return (env,tyc)

#
# readML
#
# Reads a series of MiniML entries (entered by the user) breaking them
# into a series of expressions, possible with some partial entry at
# the end. These are broken up according to presence of a semicolon.
#
# Gives back a pair: a list of strings corresponding to each complete
# entry, along with the string of the (last) partial entry.
#
def readML(entry):
    entry += input("- ") + '\n'
    while ";" not in entry:
        entry += input("= ") + '\n'
    entries = entry[:-1].split(";")
    entry = entries[-1]
    del entries[-1]
    return (entries,entry)

# 
# loadAll
#
# Reads a series of MiniML source files, whose names are in the list
# `files`, parsing them and evaluating their defintions. Their defined
# names are added to the given value and type contexts, and those 
# extended contexts are returned.
#
def loadAll(files,env,tyc):
    try:
        # Load definitions from the specified source files.
        for fname in files:
            print("[opening "+fname+"]")
            dfns = parseFile(fname)
            (env,tyc) = topBindAll(env,tyc,dfns)
    except SyntaxError as e:
        print("Syntax error.")
        print(e.args[0])
        print("Bailing command-line loading.")
    except LexError as e:
        print("Bad token reached.")
        print(e.args[0])
        print("Bailing command-line loading.")
    return (env,tyc)

#
# REPL
#
# This performs the "read-eval-print" loop of the MiniML interpreter.
# It reads an entry or a series of entries, ending/seprated by
# semi-colons, parses them as a definition term, and then type checks
# each definition, and then evaluates and binds each definition,
# adding it to the "global" value and type contexts.
#
# This continues until the user hits "Control-d" to exit.
#
# MiniML errors are reported along the way--whether they be syntactic
# errors, type errors, or runtime errors that occur during evaluation.
#
def REPL(env,tyc):
    # Interactively process entered definitions and expressions.
    done = False
    entry = ""
    while not done:
        try:
            entries,entry = readML(entry)
            for ent in entries:
                dfn = parseEntry(ent)
                (env,tyc) = topBind(env,tyc,dfn)
        except EOFError:
            done = True
        except SyntaxError as e:
            print("Syntax error.")
            print(e.args[0])
            entry = ""
        except LexError as e:
            print("Bad token reached.")
            print(e.args[0])
            entry = ""

#
#  usage: 
#    python3 miniml.py <file 1> ... <file n>
#
#      - this runs the interpreter against the specified .mml files
#
print("Mini-ML of Portlandia v2021.2 [for Reed CSCI 384 F21]")
(env,tyc) = ([],[])
(env,tyc) = loadAll(sys.argv[1:],env,tyc)
REPL(env,tyc)
