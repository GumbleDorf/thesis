from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine, ClauseDB
from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
from random import choice
from itertools import groupby
from copy import deepcopy
from world import World
from randomWorld import RandomWorld

#This is just a preliminary program to solve Monty Hall, not generalised yet.
class GDLIIIProblogRep(object):
    def __init__(self, program):
        #GlobalEngine
        self._engine = DefaultEngine()
        # For now, just use the written model
        #baseModelFile = generateProblogStringFromGDLIII(program)
        #self._baseModelFile = PrologFile('./model.prob')
        self._baseModelFile = PrologFile('./guessmodel.prob')
        self._playerList = []
        self._randomIdentifier = Constant(0) #Hardcoded to give the random player a specific constant id as we apply some special rules to the random player
        self._playerWorlds = self._initialiseKB()
        self._moveList = dict([(i,None) for i in self._playerList])
        for i in self._playerList:
            self._moveList[i] = None
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
            legalMoves[player] = set()
            for world in self._playerWorlds[player]:
                legalMoves[player] = world.query([Term('legal', player, Var('_'))])
                break
        return legalMoves

    #Assumption, term contains a single argument
    def extractSingleArg(self,nArg, term):
        return term.args[nArg]

    def query(self, player, query):
        initialResults = []
        for world in self._playerWorlds[player]:
            initialResults.append(world.query([Term('knows', player, Term('step', Constant(self._step)), query)]))
        keys = set([i for d in initialResults for i in d.keys()])
        queryResults = {}
        for k in keys:
            queryResults[k] = 0
            for d in initialResults:
                if k in d.keys():
                    queryResults[k] += d[k]

        return queryResults

    #Private
    def _initialiseKB(self):
        kb = self._engine.prepare(self._baseModelFile)
        initialState = \
            set(map(lambda a: Term('ptrue', a[0].args[0]), self._engine.ground_all(kb, queries=[Term('init',Var('_'))]).get_names()))
        players = \
            set(map(lambda a: a[0], self._engine.ground_all(kb, queries=[Term('role',Var('_'))]).get_names()))
        playerWorldState = {}

        for playerNum in map(lambda a: a.args[0], players):
            self._playerList.append(playerNum)
            knowledge = map(lambda a: Term('knows', playerNum, Term('step', Constant(1)), a.args[0]), initialState)
            playerPreds = initialState.union(set(knowledge))
            #Each player starts with a single initial world
            if playerNum == self._randomIdentifier:
                #TODO: Replace with random specific world
                playerWorldState[playerNum] = [World(self._engine, self._baseModelFile, 1, 1, playerPreds, playerNum)]
            else:
                playerWorldState[playerNum] = [World(self._engine, self._baseModelFile, 1, 1, playerPreds, playerNum)]

        return playerWorldState

    def applyActionsToModelAndUpdate(self):
        if (None in self._moveList.values()):
            raise "Error: Must have submitted moves for all players before proceeding"
        for i in self._playerList:
            newWorlds = set()
            for world in self._playerWorlds[i]:
                newWorlds = newWorlds.union(world.getSuccessorWorlds(self._moveList))
            self._playerWorlds[i] = self._normaliseProbability(newWorlds)
        self._currentLegalMoves = self._generateLegalMoves()
        self._step += 1
        self._moveList = dict([(i,None) for i in self._playerList])

    def submitAction(self, action, player):
        print(action)
        if ( action not in self._currentLegalMoves[player]):
            raise Exception
        self._moveList[player] = action

    def getPlayerIds(self):
        return [i for i in self._playerWorlds.keys()]

    #Normalise a set of probabilities assuming the probabilities in fluentProbs = 1
    #Private
    def _normaliseProbability(self,worlds):
        totalprob = 0
        for w in worlds:
            totalprob += w._prob
        for w in worlds:
            w._prob = w._prob / totalprob
        return worlds

    

#Test function to demonstrate playing monty hall with the model
def playMonty():
    model = GDLIIIProblogRep('montyhall.gdliii')
    #Playing sequentially just for demonstration
    for _ in range(3):
        playerMoves = tuple(model.getLegalMovesForPlayer(Constant(1)))
        randomMoves = tuple(model.getLegalMovesForPlayer(Constant(0)))
        model.submitAction(choice(playerMoves), Constant(1))
        model.submitAction(choice(randomMoves), Constant(0))
        model.applyActionsToModelAndUpdate()
    result = model.query(Constant(1),Term('goal', Constant(1), Constant(100)))
    print(result)


#Test function to demonstrate playing monty hall with the model
def playGuessing():
    model = GDLIIIProblogRep('guess.gdliii')
    #Playing sequentially just for demonstration
    for _ in range(3):
        playerMoves = tuple(model.getLegalMovesForPlayer(Constant(1)))
        randomMoves = tuple(model.getLegalMovesForPlayer(Constant(0)))
        model.submitAction(choice(playerMoves), Constant(1))
        model.submitAction(choice(randomMoves), Constant(0))
        model.applyActionsToModelAndUpdate()
    result = model.query(Constant(1),Term('goal', Constant(1), Constant(100)))
    print(result)



#playMonty()
playGuessing()
