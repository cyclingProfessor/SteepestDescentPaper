from __future__ import print_function
import random
import signal
import sys
import time
import copy
from collections import defaultdict
import itertools

##############################################################################
# Works in either python2 or python3
# Usage: python pathBestDescent.py [length]
#   where the (optional) length parameter is the number of (real) variables
#   before they are encoded into sets of four Boolean variables.
# Press Ctrl-C to stop the program at any time.
###############################################################################
finished = False
def signal_handler(signal, frame):
    global finished
    print('You pressed Ctrl+C!')
    finished = True

def main():
    signal.signal(signal.SIGINT, signal_handler)
    length = int(sys.argv[1]) if len(sys.argv) > 1 else 10

    boolean = Domain('ZeroOne',['0','1'])

    # We have a Boolean encoding of the values 0, 1, < and X
    # For tidyness we print them out as two characters (like 00) 
    #   so that intermediate values (like 0<) do not affect alignment
    # Really we are interested in the "symbols": 1000 (0), 0100 (1), 0010 (<) and 0001 (X)
    # 1000 => 00
    # 0100 => 11
    # 0010 => <<
    # 0001 => XX
    Zero = ('1', '0','0','0')
    One = ('0', '1','0','0')
    Carry = ('0', '0','1','0')
    Stop = ('0', '0','0','1')
    # All weight 2 words are intermediate values
    # Weights 0,3 and 4 are not allowed.
    ZeroOne = tuple(max (*l) for l in zip(Zero,One))
    OneCarry = tuple(max (*l) for l in zip(Carry,One))
    ZeroStop = tuple(max (*l) for l in zip(Zero,Stop))
    ZeroCarry = tuple(max (*l) for l in zip(Zero,Carry))
    OneStop = tuple(max (*l) for l in zip(One, Stop))

    # The main cost function f:
    funF = CostFunction('funF', tuple([boolean] * 8))
    funH = CostFunction('funH', tuple([boolean] * 4))
    for s in (One, Zero):
        funF.setCost(One + s, 4)
        funF.setCost(Carry + s, 6)
    funF.setCost(Zero + Carry, 13)
    funF.setCost(Zero + Stop, 13)
    funF.setCost(Carry + Stop, 8)

    # Now the fixes for f in the presence of intermediate values
    funF.setCost(Carry + OneCarry, 23)
    funF.setCost(Carry + ZeroStop, 7)
    funF.setCost(Zero + OneStop, 14)
    funF.setCost(ZeroCarry + Stop, 12)
    funF.setCost(ZeroCarry + Carry, 8)

    # Allow a starting move. Valued function h
    funH.setCost(ZeroOne, 1)
    funH.setCost(OneCarry, 5)

    Vars = []
    for index in range(4 * length):
        nextV = Variable('name' + str(index), boolean)
        Vars.append(nextV)
        if index %4 == 0:
            nextV.setValue('1')

    Constraints = []
    weight = 1
    for index in range(length - 1):
        print(index)
        Constraints.append(Constraint('f' + str(index), Vars[4 *index:4 * index + 8], funF, weight))
        weight *= 4

    Constraints.append(Constraint('h', Vars[0:4], funH, 1))

    specPath = Instance(Vars, Constraints)
    printSpec(list(map(lambda v: v.getValue(), Vars)))

    experiment = 0
    move = specPath.bestImprove()
    while not finished and len(move) > 0:
        move[0].setValue(move[1])
        printSpec(list(map(lambda v: v.getValue(), Vars)))
        experiment += 1
        move = specPath.bestImprove()
        # time.sleep(0.1)
    print("finished iteration ", experiment, " and exited")

####################################################################

def printSpec(list):
    names = ['0', '1', '<', 'X']
    for index in range(0, len(list), 4):
        first = list[index: index + 4].index('1')
        print(names[first], end='')
        if list[index: index + 4].count('1') > 1:
            second = list[index + first + 1: index + 4].index('1')
            print(names[first + 1 + second], end=' ')
        else:
            print(' ', end=' ')
    print

class BadArgs(Exception):
    def __init__(self, message):
        self.message = message

class Instance:
    def __init__(self, variables, constraints):
        self._variables = variables
        self._constraints = constraints
        self._value = 0
        for c in constraints:
            c.addChangeObserver(self)
            self._value += c.value()
    def delta(self, change):
        self._value += change
    def value(self):
        return self._value
    def orderedImprove(self):
        currentValue = self._value
        for v in self._variables:
            oldValue = v.getValue()
            for d in v:
                v.setValue(d)
                if self._value > currentValue:
                    v.setValue(oldValue)
                    return (v,d)
            v.setValue(oldValue)
        return ()

    def bestImprove(self):
        bestMove = ()
        currentBest = self._value;
        print('Current Fitness:' + str(currentBest))
        for v in self._variables:
            oldValue = v.getValue()
            for d in v:
                v.setValue(d)
                if self._value > currentBest + 0.001:
                    currentBest = self._value;
                    bestMove = (v,d)
            v.setValue(oldValue)
        return bestMove
    def __str__(self):
        retval = '{'
        for v in self._variables:
            retval += str(v)
        return retval + '}'


# An iterable list of printable values
class Domain:
    def __init__(self, name, values):
        self._name = name
        self._values = values
    def getName(self):
        return self._name
    def getDefault(self):
        return self._values[0]
    def __iter__(self):
        return iter(self._values)

class Constraint:
    def __init__(self, name, vars, costs, weight):
        # Check that the cost function has the right domains
        if costs.getDomains() != tuple(v.getDomain() for v in vars):
            raise BadArgs("Variable Domains don't match Cost Function when creating a Constraint")
        self._scope = vars
        self._name = name
        self._cf = costs
        self._wt = weight
        self._observers = []
        self._currentValue = self._wt * self._cf.getCost(tuple(v.getValue() for v in self._scope))
        for v in self._scope:
            v.addChangeObserver(self)
    def getScope(self):
        return self._scope;
    def addChangeObserver(self, who):
        self._observers.append(who)
    def changed(self):
        oldValue = self._currentValue
        self._currentValue = self._wt * self._cf.getCost(tuple(v.getValue() for v in self._scope))
        for o in self._observers:
            o.delta(self._currentValue - oldValue)
    def inScope(self, var):
        return var in self._scope
    def value(self):
        return self._currentValue 

# A Variable has a domain, a name and a value.  The "value" is an index into that domain
# All variables begin with a default value (index) of 0
class Variable:
    def __init__(self, name, domain):
        self._name = name
        self._domain = domain
        self._observers = []
        self._value = self._domain.getDefault()
    def __iter__(self):
        return iter(self._domain)
    def getName(self):
        return self._name
    def getDomain(self):
        return self._domain
    def addChangeObserver(self, who):
        self._observers.append(who)
    def setValue(self, v):
        if self._value != v:
            self._value = v
            for o in self._observers:
                o.changed()
    def getValue(self):
        return self._value
    def __str__(self):
        return "[" + str(self._value) + "]"

# A cost function has a scope which is a list of domains.
# It is a mapping from assignments to values
# Cost functions can be shared. 
class CostFunction:
    def __init__(self, name, domains):
        # Check that all domains are actually Domains
        self._name = name
        self._domains = domains
        self._costMatrix = {t:0 for t in itertools.product(*domains)}
    def setCost(self, t, value):
        self._costMatrix[t] = value
    def getDomains(self):
        return self._domains
    def getCost(self, t):
        return self._costMatrix[t]
    def __str__(self):
        return "(" + self._name + ")"

if __name__ == "__main__":
    main()
