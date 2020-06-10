from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine
from problog.logic import Term, Constant,Var
from problog import get_evaluatable

from mdpprolog import Engine
#This is just a preliminary program to solvce Monty Hall, not generalised yet.

#Step 1, add init to kb
#Step 2, take in an action from
def generateProblogModelFromGDLIII():
    pass


#Normalise a set of probabilities assuming the probabilities in fluentProbs = 1
def normaliseProbability(fluentProbs):
    totalprob = 0
    for clause, prob in fluentProbs:
        totalprob += prob
    normalisedProbs = {}
    for clause, prob in fluentProbs:
        normalisedProbs[clause] = prob/totalprob
    return normalisedProbs


def initialiseKB():

    db = Engine(open('init_model.txt').read())
    #a = program.query(db, Term('a',Var('_')))
    db.relevant_ground([Term('a', Var('_'))])
    print(db._gp.get)
    
    e = db.evaluate(db.compile(),{})

    print(e)

def getNodesWithWeights(db):
    e = db.get_names()
    r = db.get_weights()
    retVals = {}
    for (k,v) in e:
        retVals[k] = r[v]
    return retVals

    
    

initialiseKB()