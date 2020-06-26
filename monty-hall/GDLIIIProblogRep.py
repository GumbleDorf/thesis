from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine, ClauseDB
from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
from random import choice
from itertools import groupby
from copy import deepcopy

#This is just a preliminary program to solve Monty Hall, not generalised yet.
class GDLIIIProblogRep(object):
    def __init__(self, program):
        #GlobalEngine
        self._engine = DefaultEngine()
        # For now, just use the written model
        #baseModelFile = generateProblogStringFromGDLIII(program)
        self._baseModelFile = PrologFile('./model.prob')
        self._playerList = []
        self._kb = self._engine.prepare(self._baseModelFile)
        self._playerWorlds = self._initialiseKB()
        self._randomIdentifier = Constant(0) #Hardcoded to give the random player a specific constant id as we apply some special rules to the random player
        self._moveList = {}
        self._completeState = []
        self._currentLegalMoves = self._generateLegalMoves()
        self._step = 1

    def getMoveList(self):
        return self._moveList

    def getLegalMovesForPlayer(self, player):
        return self._currentLegalMoves[player]

    def _resetKnowledgeBase(self):
        self._kb = self._engine.prepare(self._baseModelFile)

    def generateProblogStringFromGDLIII(self):
        pass

    def getPlayersPossibleWorlds(self, player):
        return self._playerWorlds[player]

    def _generateLegalMoves(self):
        legalMoves = {}
        for player in self._playerWorlds.keys():
            legalMoves[player] = \
            list(map(lambda x: x[0], self._getQueryAsTupleWithProbabilities(
                [Term('legal',player,Var('_'))],\
                self._kb, \
                lambda x: self.extractSingleArg(1,x)\
            )))
        return legalMoves

    #Assumption, term contains a single argument
    def extractSingleArg(self,nArg, term):
        return term.args[nArg]

    def _regenKb(self, preds):
        newKb = self._engine.prepare(self._baseModelFile)
        for i in preds:
            newKb.add_fact(i)

        return newKb

    #Normalise a set of probabilities assuming the probabilities in fluentProbs = 1
    #Private
    def _initialiseKB(self):
        initialState = \
            self._getQueryAsTupleWithProbabilities([Term('init',Var('_'))],self._kb, lambda x: self.extractSingleArg(0,x))
        players = \
            self._getQueryAsTupleWithProbabilities([Term('role',Var('_'))],self._kb, lambda x: self.extractSingleArg(0,x))
        playerWorldState = {}

        for playerNum,_ in players:
            self._playerList.append(playerNum)
            #Worlds are contstructed in a tuple as (Probability of being true world, set of fluents true in that world)
            playerWorldState[playerNum] = [(1,set(map(lambda a: (Term('knows', playerNum, \
                Term('step', Constant(1)),a[0]), a[1]),initialState)))]

        self._completeState = initialState

        return playerWorldState

    def submitAction(self, action, player):
        print(action)
        if ( action not in self._currentLegalMoves[player]):
            raise Exception
        self._moveList[player] = action
        pass

    def getPlayerIds(self):
        return [i for i in self._playerWorlds.keys()]

    #Normalise a set of probabilities assuming the probabilities in fluentProbs = 1
    #Private
    def _normaliseProbability(self,worldProbs):
        totalprob = 0
        for prob, world in worldProbs:
            totalprob += prob
        normalisedProbs = []
        for prob, world in worldProbs:
            normalisedProbs.append((prob/totalprob, world))
        return normalisedProbs
    
    def _getQueryAsTupleWithProbabilities(self, queries, database, function = lambda x: x):
        return self._getNodesWithWeights(self._relevantGround(queries,database),function)
    
    def query(self, queries):
        return self._getQueryAsTupleWithProbabilities(queries, self._kb)
    #Private
    def _relevantGround(self, queries, database):
        return self._engine.ground_all(database, queries=queries)

    def getNormalisedKnowledge(self, knowledge):
        pass

#Test function to demonstrate playing monty hall with the model
def playMonty(model):
    #Playing sequentially just for demonstration
    for _ in range(3):
        playerMoves = model.getLegalMovesForPlayer(Constant(1))
        randomMoves = model.getLegalMovesForPlayer(Constant(0))
        model.submitAction(playerMoves[0], Constant(1))
        model.submitAction(choice(randomMoves), Constant(0))
        model.applyActionsToModelAndUpdate()
        print(model.getPlayersPossibleWorlds(Constant(1)))
    result = model.query([Term('goal', Constant(1), Var("_"))])
    print(result)
    return 1


r = GDLIIIProblogRep('montyhall.gdliii')
print(r.query([Term('knows', Constant(1), Var('_'), Var('_'))]))
#playMonty(r)
