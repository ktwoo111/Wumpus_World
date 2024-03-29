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


    modelFromAddKnow = {} #model to put in the literals that we already know
    # Create the knowledge base with wumpus rules
    print '\nLoading wumpus rules...'
    knowledge_base = logical_expression()
    knowledge_base.connective = ['and']
    for line in input_file:
        # Skip comments and blank lines. Consider all line ending types.
        if line[0] == '#' or line == '\r\n' or line == '\n' or line == '\r':
            continue
        counter = [0]  # A mutable counter so recursive calls don't just make a copy

        temp = line
        splitted = temp.split(" ")
        #for elem in splitted:
        #    print elem
        if len(splitted) == 2:
            if "not" in temp.lower():
                splitted = temp.split(" ")
                splitted[1] = splitted[1].rstrip('\r\n')
                splitted[1] = splitted[1].rstrip('\r')
                splitted[1] = splitted[1].rstrip(')')
                if splitted[1] not in modelFromAddKnow.keys():
                    modelFromAddKnow[splitted[1]] = False
        if len(splitted) == 1:
            splitted[0] = splitted[0].rstrip('\r\n')
            splitted[0] = splitted[0].rstrip('\r')
            splitted[0] = splitted[0].rstrip(')')
            if splitted[0] not in modelFromAddKnow.keys():
                modelFromAddKnow[splitted[0]] = True


        subexpression = read_expression(line.rstrip('\r\n'), counter)
        knowledge_base.subexpressions.append(subexpression)
    input_file.close()

    #print 'from rules ', modelFromAddKnow #TODO: testing
    # Read additional knowledge base information file
    try:
        input_file = open(argv[2], 'rb')
    except:
        print('failed to open file %s' % argv[2])
        sys.exit(0)



    # I had left this line out of the original code. If things break, comment out.
    #print_expression(knowledge_base, '\n') #TODO: testing
    #print

    #print 'from rule ', modelFromAddKnow  # TODO: testing
    #print 'size of dictionary ', len(modelFromAddKnow) # TODO:testing


    # Add expressions to knowledge base
    print 'Loading additional knowledge...'
    for line in input_file:
        # Skip comments and blank lines. Consider all line ending types.
        if line[0] == '#' or line == '\r\n' or line == '\n' or line == '\r':
            continue
        counter = [0]  # a mutable counter

        temp = line
        splitted = temp.split(" ")
        #for elem in splitted:
        #    print elem
        if len(splitted) == 2:
            if "not" in temp.lower():
                splitted = temp.split(" ")
                splitted[1] = splitted[1].rstrip('\r\n')
                splitted[1] = splitted[1].rstrip('\r')
                splitted[1] = splitted[1].rstrip(')')
                if splitted[1] not in modelFromAddKnow.keys():
                    modelFromAddKnow[splitted[1]] = False
        if len(splitted) == 1:
            splitted[0] = splitted[0].rstrip('\r\n')
            splitted[0] = splitted[0].rstrip('\r')
            splitted[0] = splitted[0].rstrip(')')
            if splitted[0] not in modelFromAddKnow.keys():
                modelFromAddKnow[splitted[0]] = True

        subexpression = read_expression(line.rstrip('\r\n'), counter)
        knowledge_base.subexpressions.append(subexpression)
    input_file.close()

    # Verify it is a valid logical expression
    if not valid_expression(knowledge_base):
        sys.exit('invalid knowledge base')

    # I had left this line out of the original code. If things break, comment out.
    #print_expression(knowledge_base, '\n') #TODO: testing
    #print 'from additional and rule ', modelFromAddKnow #TODO: testing
    #print 'size of dictionary ', len(modelFromAddKnow) #TODO:testing
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
    #print_expression(statement, '') #TODO: testing
    print

    # Run the statement through the inference engine
    check_true_false(knowledge_base, statement, modelFromAddKnow)
    sys.exit(1)
    

if __name__ == '__main__':
    main(sys.argv)
