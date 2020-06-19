from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine, ClauseDB
from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
from random import choice
import itertools
from copy import deepcopy
#This is just a preliminary program to solve Monty Hall, not generalised yet.
class GDLIIIProblogRep(object):
    def __init__(self, program):
        self._playerKnowledge = {}
        self._engine = DefaultEngine()
        self._addedPreds = []
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

    # Requires a valid move from all players
    # :param moves: dictionary of constant ids of players to a single move
    # :type moves: dictionary problog Constant -> problog Term
    def applyActionsToModelAndUpdate(self):
        for player in self._moveList.keys():
            self._addFact(Term('does',player, self._moveList[player]))
        for (fact, prob) in self._completeState:
            self._addFact(Term('ptrue',fact), probability=prob)
        self._completeState = self._getQueryAsTupleWithProbabilities([Term('next',Var('_'))], self._kb, lambda x: self.extractSingleArg(0,x))
        
        self._step += 1
        #Update player knowledge (just player 1 at the moment, will add support for more players later)
        for player in self._playerList:
            if (player == self._randomIdentifier): continue
            updatedWorlds = []
            for world in self._playerWorlds[player]:
                newWorlds = self._generateNewPossibleWorld(world, player)
                updatedWorlds.extend(newWorlds)
            self._playerWorlds[player] = self._normaliseProbability(updatedWorlds)

        self._resetKnowledgeBase()
        self._applyTrueStateToModel()
        if (len(self.query([Constant('terminal')])) == 0):
            self._currentLegalMoves = self._generateLegalMoves()

    #Assumption, term contains a single argument
    def extractSingleArg(self,nArg, term):
        return term.args[nArg]

    def _forkkb(self):
        newKb = self._engine.prepare(self._baseModelFile)
        for i in self._addedPreds:
            newKb.add_fact(i)

        return newKb

    def _generateNewPossibleWorld(self, world, player):
        prob, world_fluents = world
        worldCopy = self._forkkb()
        for fact, _ in world_fluents:
            worldCopy.add_fact(fact)

        updates = self._getQueryAsTupleWithProbabilities([Term('update',Var('_'))],worldCopy, lambda a : self.extractSingleArg(0,a))

        updates = [i for i in updates if i[0].signature == "knows/2"]
        kbReps = set(map(lambda a: a[0], world_fluents))
        #Hardcode for monty hall atm, will make a more general version later
        newWorlds = []
        constPreds = set([i for i in updates if i[1] == 1])
        varPreds = set([i for i in updates if i[1] != 1])
        for i in varPreds:
            conWorld = constPreds - set([(Term('step', Constant(self._step - 1)), 1)])
            probVal = world[0]
            if (type(i[1]) == int):
                probVal *= i[1]
            else:
                probVal *= i[1].value
            conWorld.add(i)
            conWorld.add((Term('knows', player, Term('step', Constant(self._step))), 1))
            predictions = self._getQueryAsTupleWithProbabilities([Term('correct',Var('_'))],worldCopy, lambda a : self.extractSingleArg(0,a))
            if len(predictions) == 0 or len(set(map(lambda a: a[0], predictions)).intersection(set(map(lambda a: a[0],conWorld)))) > 0:
                newWorlds.append((probVal, conWorld))
            

        return newWorlds

    # Transform a query response to a list of terms and probabilities
    def _getNodesWithWeights(self,res, function = lambda x: x):
        names = res.get_names()
        weights = res.get_weights()
        retVals = []

        for (k,v) in names:
            if v is None:
                continue
            if (v == 0):
                retVals.append((function(k), 1))
            else:
                retVals.append((function(k), weights[v]))
        return retVals

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
            playerWorldState[playerNum] = [(1,set(map(lambda a: (Term('knows', playerNum, a[0]), a[1]),initialState)))]

        self._completeState = initialState
        self._applyTrueStateToModel()
        return playerWorldState

    def _applyTrueStateToModel(self):
        for pred, prob in self._completeState:
            self._addFact(Term('ptrue', pred), prob)

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

    def _addFact(self, term, probability=None):
        self._addedPreds.append(term)
        return self._kb.add_fact(term)

    
    def _addRule(self, head, body):
        b = body[0]
        for term in body[1:]:
            b = b & term
        rule = head << b
        self._addedPreds.append(rule)
        return self._kb.add_clause(rule)
    
    def _getQueryAsTupleWithProbabilities(self, queries, database, function = lambda x: x):
        return self._getNodesWithWeights(self._relevantGround(queries,database),function)
    
    def query(self, queries):
        return self._getQueryAsTupleWithProbabilities(queries, self._kb)
    #Private
    def _relevantGround(self, queries, database):
        return self._engine.ground_all(database, queries=queries)

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
playMonty(r)
