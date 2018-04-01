#!/usr/bin/env python

#-------------------------------------------------------------------------------
# Name:        check_true_false
# Purpose:     Main entry into logic program. Reads input files, creates 
#              base, tests statement, and generates result file.
#
# Created:     09/25/2011
# Last Edited: 07/22/2013     
# Notes:       *Ported by Christopher Conly from C++ code supplied by Dr. 
#               Vassilis Athitsos.
#              *Several integer and string variables are put into lists. This is
#               to make them mutable so each recursive call to a function can
#               alter the same variable instead of a copy. Python won't let us
#               pass the address of the variables, so I put it in a list, which
#               is passed by reference.
#              *Written to be Python 2.4 compliant for omega.uta.edu
#-------------------------------------------------------------------------------

import sys
from logical_expression import *


def TT_Entails(KB, alpha):
    KBsymbols = ExtractSymbol(KB)
    Alphasymbols = ExtractSymbol(alpha)
    symbols = KBsymbols + Alphasymbols
    symbols = sorted(set(symbols),key=symbols.index)
    print symbols #TODO: testing
    model = {}
    return TT_Check_All(KB,alpha,symbols,{})





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

        trueModel = model
        trueModel[P] = True

        falseModel = model
        falseModel[P] = False

        return TT_Check_All(KB,alpha,rest, trueModel) and TT_Check_All(KB,alpha,rest,falseModel)
def PL_True(expression, model):
    if expression.symbol[0] is not '':
        return model[expression.symbol[0]]
    elif expression.connective[0].lower() is "and":
        for elem in expression.subexpressions:
            if PL_True(elem,model) is False:
                return False
        return True
    elif expression.connective[0].lower() is "or":
        for elem in expression.subexpressions:
            if PL_True(elem,model) is True:
                return True
        return False
    elif expression.connective[0].lower() is "xor":
        true_trigger = False
        false_trigger = False
        for elem in expression.subexpressions:
            if PL_True(elem,model) is True:
                true_trigger = True
            else:
                false_trigger = True
        if true_trigger is True and false_trigger is True:
            return True
        else:
            return False
    elif expression.connective[0].lower() is "if":
        one = expression.subexpressions[0]
        two = expression.subexpressions[1]
        if PL_True(one,model) is True and PL_True(two,model) is False:
            return False
        else:
            return True
    elif expression.connective[0].lower() is "iff":
        one = expression.subexpressions[0]
        two = expression.subexpressions[1]
        if PL_True(one,model) == PL_True(two,model):
            return True
        else:
            return False
    elif expression.connective[0].lower() is "not":
        one = expression.subexpressions[0]
        if PL_True(one, model) is True:
            return False
        else:
            return True



def main(argv):
    if len(argv) != 4:
        print('Usage: %s [wumpus-rules-file] [additional-knowledge-file] [input_file]' % argv[0])
        sys.exit(0)

    # Read wumpus rules file
    try:
        input_file = open(argv[1], 'rb')
    except:
        print('failed to open file %s' % argv[1])
        sys.exit(0)

    # Create the knowledge base with wumpus rules
    print '\nLoading wumpus rules...'
    knowledge_base = logical_expression()
    knowledge_base.connective = ['and']
    for line in input_file:
        # Skip comments and blank lines. Consider all line ending types.
        if line[0] == '#' or line == '\r\n' or line == '\n' or line == '\r':
            continue
        counter = [0]  # A mutable counter so recursive calls don't just make a copy
        subexpression = read_expression(line.rstrip('\r\n'), counter)
        knowledge_base.subexpressions.append(subexpression)
    input_file.close()

    # Read additional knowledge base information file
    try:
        input_file = open(argv[2], 'rb')
    except:
        print('failed to open file %s' % argv[2])
        sys.exit(0)



    # I had left this line out of the original code. If things break, comment out.
    print_expression(knowledge_base, '\n')
    print


    # Add expressions to knowledge base
    print 'Loading additional knowledge...'
    for line in input_file:
        # Skip comments and blank lines. Consider all line ending types.
        if line[0] == '#' or line == '\r\n' or line == '\n' or line == '\r':
            continue
        counter = [0]  # a mutable counter
        subexpression = read_expression(line.rstrip('\r\n'), counter)
        knowledge_base.subexpressions.append(subexpression)
    input_file.close()

    # Verify it is a valid logical expression
    if not valid_expression(knowledge_base):
        sys.exit('invalid knowledge base')

    # I had left this line out of the original code. If things break, comment out.
    print_expression(knowledge_base, '\n')

    # Read statement whose entailment we want to determine
    try:
        input_file = open(argv[3], 'rb')
    except:
        print('failed to open file %s' % argv[3])
        sys.exit(0)

    print
    print 'Loading statement...'
    statement = input_file.readline().rstrip('\r\n')
    input_file.close()
    
    # Convert statement into a logical expression and verify it is valid
    statement = read_expression(statement)
    if not valid_expression(statement):
        sys.exit('invalid statement')

    # Show us what the statement is
    print '\nChecking statement: ',
    print_expression(statement, '')
    print

    # Run the statement through the inference engine
    print TT_Entails(knowledge_base, statement)

    sys.exit(1)
    

if __name__ == '__main__':
    main(sys.argv)
