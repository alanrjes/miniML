#
# CSCI 384 Fall 2019
#
# class table - the implementation of immutable table objects
#
# Part of Homework 07.
#
# Defines the MiniML type `'a table`, an immutable data
# structure that holds a collection of key-value pairs.
# The keys are strings, and the value can be any MiniML
# data type. 
#
# Tables `t` support the following following
# constants and operations
#
#   empty       - an empty table
#   t +: (s,v)  - t along with a pair s=>v
#   t -: s      - t without a pair with key s
#   t ? s       - true/false as to whether t contains s
#   t . s       - get the value with key s
#   keys t      - get a list of the keys
#   size t      - the number of pairs in t
#
# Note that these are immutable operations and that, in
# particular, +: and -: give back the new table that 
# results from applying that operation.
#
# All these operations are implemented below in the
# following `class table`, an object class that itself
# simply relies on an underlying Python dictionary.
#
# There is an addional method `dictOf` that gives back
# that underlying dictionary.
#

class table:

    # table(T0):
    #
    # Given a Python dictionary mapping strings
    # to values, wraps it up as a table.
    #
    def __init__(self,T0 = {}):
        self.T = T0

    # t.withAlso(k,v)
    #
    # Returns a table with an added/updated entry
    # associating a key (a string) to the given
    # value.
    def withAlso(self,key,value):
        t = {k:self.T[k] for k in self.T}
        t[key] = value
        return table(t)

    # t.contains(k)
    #
    # Returns a boolean indicating whether the 
    # table has an entry for the given string.
    #
    def contains(self,key):
        return (key in self.T)

    # t.lookUp(k)
    #
    # Returns the value associated with the given
    # string.
    #
    def lookUp(self,key):
        return self.T[key]

    # t.size()
    #
    # Returns the number of entries in the table.
    #
    def size(self):
        return len(self.T)

    # t.size()
    #
    # Returns the list of strings that are keys in
    # the table.
    #
    def keys(self):
        return [k for k in self.T]

    # t.without()
    #
    # Returns a new table with the given string's
    # entry removed.  The key does not have to be
    # in the table.
    #
    def without(self,key):
        if key in self.T:
            t = {k:self.T[k] for k in self.T}
            del t[key]
            return table(t)
        else:
            return self

    # t.dictOf():
    # 
    # Gives back the underlying dictionary of the table.
    #
    def dictOf(self):
        return self.T

