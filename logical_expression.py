#!/usr/bin/env python

#-------------------------------------------------------------------------------
# Name:        logical_expression
# Purpose:     Contains logical_expression class, inference engine,
#              and assorted functions
#
# Created:     09/25/2011
# Last Edited: 07/22/2013  
# Notes:       *This contains code ported by Christopher Conly from C++ code
#               provided by Dr. Vassilis Athitsos
#              *Several integer and string variables are put into lists. This is
#               to make them mutable so each recursive call to a function can
#               alter the same variable instead of a copy. Python won't let us
#               pass the address of the variables, so put it in a list which is
#               passed by reference. We can also now pass just one variable in
#               the class and the function will modify the class instead of a
#               copy of that variable. So, be sure to pass the entire list to a
#               function (i.e. if we have an instance of logical_expression
#               called le, we'd call foo(le.symbol,...). If foo needs to modify
#               le.symbol, it will need to index it (i.e. le.symbol[0]) so that
#               the change will persist.
#              *Written to be Python 2.4 compliant for omega.uta.edu
#-------------------------------------------------------------------------------

import sys
from copy import copy

#-------------------------------------------------------------------------------
# Begin code that is ported from code provided by Dr. Athitsos
class logical_expression:
    """A logical statement/sentence/expression class"""
    # All types need to be mutable, so we don't have to pass in the whole class.
    # We can just pass, for example, the symbol variable to a function, and the
    # function's changes will actually alter the class variable. Thus, lists.
    def __init__(self):
        self.symbol = ['']
        self.connective = ['']
        self.subexpressions = []


def print_expression(expression, separator):
    """Prints the given expression using the given separator"""
    if expression == 0 or expression == None or expression == '':
        print '\nINVALID\n'

    elif expression.symbol[0]: # If it is a base case (symbol)
        sys.stdout.write('%s' % expression.symbol[0])

    else: # Otherwise it is a subexpression
        sys.stdout.write('(%s' % expression.connective[0])
        for subexpression in expression.subexpressions:
            sys.stdout.write(' ')
            print_expression(subexpression, '')
            sys.stdout.write('%s' % separator)
        sys.stdout.write(')')


def read_expression(input_string, counter=[0]):
    """Reads the next logical expression in input_string"""
    # Note: counter is a list because it needs to be a mutable object so the
    # recursive calls can change it, since we can't pass the address in Python.
    result = logical_expression()
    length = len(input_string)
    while True:
        if counter[0] >= length:
            break

        if input_string[counter[0]] == ' ':    # Skip whitespace
            counter[0] += 1
            continue

        elif input_string[counter[0]] == '(':  # It's the beginning of a connective
            counter[0] += 1
            read_word(input_string, counter, result.connective)
            read_subexpressions(input_string, counter, result.subexpressions)
            break

        else:  # It is a word
            read_word(input_string, counter, result.symbol)
            break
    return result


def read_subexpressions(input_string, counter, subexpressions):
    """Reads a subexpression from input_string"""
    length = len(input_string)
    while True:
        if counter[0] >= length:
            print '\nUnexpected end of input.\n'
            return 0

        if input_string[counter[0]] == ' ':     # Skip whitespace
            counter[0] += 1
            continue

        if input_string[counter[0]] == ')':     # We are done
            counter[0] += 1
            return 1

        else:
            expression = read_expression(input_string, counter)
            subexpressions.append(expression)


def read_word(input_string, counter, target):
    """Reads the next word of an input string and stores it in target"""
    word = ''
    while True:
        if counter[0] >= len(input_string):
            break

        if input_string[counter[0]].isalnum() or input_string[counter[0]] == '_':
            target[0] += input_string[counter[0]]
            counter[0] += 1

        elif input_string[counter[0]] == ')' or input_string[counter[0]] == ' ':
            break

        else:
            print('Unexpected character %s.' % input_string[counter[0]])
            sys.exit(1)


def valid_expression(expression):
    """Determines if the given expression is valid according to our rules"""
    if expression.symbol[0]:
        return valid_symbol(expression.symbol[0])

    if expression.connective[0].lower() == 'if' or expression.connective[0].lower() == 'iff':
        if len(expression.subexpressions) != 2:
            print('Error: connective "%s" with %d arguments.' %
                        (expression.connective[0], len(expression.subexpressions)))
            return 0

    elif expression.connective[0].lower() == 'not':
        if len(expression.subexpressions) != 1:
            print('Error: connective "%s" with %d arguments.' %
                        (expression.connective[0], len(expression.subexpressions)))
            return 0

    elif expression.connective[0].lower() != 'and' and \
         expression.connective[0].lower() != 'or' and \
         expression.connective[0].lower() != 'xor':
        print('Error: unknown connective %s.' % expression.connective[0])
        return 0

    for subexpression in expression.subexpressions:
        if not valid_expression(subexpression):
            return 0
    return 1


def valid_symbol(symbol):
    """Returns whether the given symbol is valid according to our rules."""
    if not symbol:
        return 0

    for s in symbol:
        if not s.isalnum() and s != '_':
            return 0
    return 1

# End of ported code
#-------------------------------------------------------------------------------

# Add all your functions here

def ExtractSymbol(expression):
    extractedSymbols = []
    if expression.symbol[0] != '':
        extractedSymbols.append(expression.symbol[0])
    else:
        for elem in expression.subexpressions:
            extractedSymbols = extractedSymbols + (ExtractSymbol(elem))
    return extractedSymbols

def RemoveSymbol(symbols,modelFromAddKnow):
    key = modelFromAddKnow.keys()

    #print 'keys ', key #TODO: testing
    #print 'dict ', modelFromAddKnow #TODO: testing

    symbols = [x for x in symbols if x not in key]

    return symbols



def TT_Entails(KB, alpha,modelFromAddKnow):
    KBsymbols = ExtractSymbol(KB)
    Alphasymbols = ExtractSymbol(alpha)
    symbols = KBsymbols + Alphasymbols
    symbols = sorted(set(symbols), key=symbols.index)
    #print symbols #TODO: testing
    #print 'size: ', len(symbols) #TODO: testing
    symbols = RemoveSymbol(symbols,modelFromAddKnow)
    #print symbols #TODO: testing
    #print 'size: ', len(symbols) #TODO: testing
    return TT_Check_All(KB,alpha,symbols,modelFromAddKnow)


#model will be a dictionary
def TT_Check_All(KB, alpha, symbols, model):

    if len(symbols) == 0:
        if PL_True(KB,model):
            return PL_True(alpha,model)
        else:
            return True
    else:
        P = symbols[0]
        rest = symbols[1:] #everything except the first index one

        trueModel = dict(model)
        trueModel[P] = True

        falseModel = dict(model)
        falseModel[P] = False

        return TT_Check_All(KB,alpha,rest, trueModel) and TT_Check_All(KB,alpha,rest,falseModel)


def PL_True(expression, model):
    if expression.symbol[0] !=  '':
        return model[expression.symbol[0]]
    elif expression.connective[0].lower() == 'and':
        for elem in expression.subexpressions:
            if PL_True(elem,model) == False:
                return False
        return True
    elif expression.connective[0].lower() == 'or':
        for elem in expression.subexpressions:
            if PL_True(elem,model) == True:
                return True
        return False
    elif expression.connective[0].lower() == 'xor':
        #An "xor" statement is true if exactly 1 substatement is true (no more, no fewer).
        true_trigger = 0
        false_trigger = 0
        for elem in expression.subexpressions:
            if PL_True(elem,model) is True:
                true_trigger = true_trigger + 1
            else:
                false_trigger = false_trigger + 1
        if true_trigger == 1 and false_trigger > 0:
            return True
        else:
            return False
    elif expression.connective[0].lower() == 'if':
        one = expression.subexpressions[0]
        two = expression.subexpressions[1]
        if PL_True(one,model) == True and PL_True(two,model) == False:
            return False
        else:
            return True
    elif expression.connective[0].lower() == 'iff':
        one = expression.subexpressions[0]
        two = expression.subexpressions[1]
        if PL_True(one,model) == PL_True(two,model):
            return True
        else:
            return False
    elif expression.connective[0].lower() == 'not':
        one = expression.subexpressions[0]
        if PL_True(one, model) == True:
            return False
        else:
            return True
def check_true_false(KB, alpha,modelFromAddKnow):
    f = open('result.txt','w')
    invAlpha = logical_expression()
    invAlpha.connective = ['NOT']
    invAlpha.subexpressions.append(alpha)
    #print_expression(alpha, '\n') #TODO: testing
    #print
    #print_expression(invAlpha,'\n') #TODO: testing
    #print #TODO: testing
    modelFromAddKnowCopy = dict(modelFromAddKnow)

    KBentailsStatement = TT_Entails(KB,alpha,modelFromAddKnow)
    KBentailsNegStatement = TT_Entails(KB,invAlpha,modelFromAddKnowCopy)

    print KBentailsStatement #TODO: Testing
    print KBentailsNegStatement #TODO: testing
    result = ''
    if KBentailsStatement == True and KBentailsNegStatement == False:
        result = "definitely true"
    elif KBentailsStatement == False and KBentailsNegStatement == True:
        result = "definitely false"
    elif KBentailsStatement == False and KBentailsNegStatement == False:
        result = "possibly true, possibly false"
    elif KBentailsStatement == True and KBentailsNegStatement == True:
        result = "both true and false"

    print result #TODO: testing
    f.write(result)
    f.close()
    return result



