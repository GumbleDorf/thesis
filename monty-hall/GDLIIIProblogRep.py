from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine, ClauseDB
from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
from random import choice
from itertools import groupby
from copy import deepcopy
from world import World
from randomWorld import RandomWorld
from GDLIIIParser import GDLIIIParser, File_Format

#This is just a preliminary program to solve Monty Hall, not generalised yet.
class GDLIIIProblogRep(object):
    def __init__(self, program):
        #GlobalEngine
        self._engine = DefaultEngine()
        # For now, just use the written model
        #baseModelFile = generateProblogStringFromGDLIII(program)
        gdl_parser = GDLIIIParser()
        self._baseModelFile = gdl_parser.output_problog(program, File_Format.INFIX)
        #self._baseModelFile = PrologFile('guessmodel.prob')
        self._playerList = []
        self._randomIdentifier = Constant(0) #Hardcoded to give the random player a specific constant id as we apply some special rules to the random player
        self._playerWorlds = self._initialiseKB()
        self._moveList = dict([(i,None) for i in self._playerList])
        for i in self._playerList:
            self._moveList[i] = None
        self._completeState = []
        self.terminal = False
        self._currentLegalMoves = self._generateLegalMoves()

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

    def _rawQuery(self, player, query):
        initialResults = []
        #Assumption: Sum of all probabilities of worlds == 1
        for world in self._playerWorlds[player]:
            initialResults.append(world.query([query]))
        keys = set([i for d in initialResults for i in d.keys()])
        queryResults = {}
        for k in keys:
            queryResults[k] = 0
            for d in initialResults:
                if k in d.keys():
                    queryResults[k] += d[k]
        return queryResults

    def query(self, player, query):
        return self._rawQuery(player, Term('thinks', player, query))

    #Private
    def _initialiseKB(self):
        self._kb = self._engine.prepare(self._baseModelFile)
        initialState = \
            set(map(lambda a: Term('ptrue', a[0].args[0]), self._engine.ground_all(self._kb, queries=[Term('init',Var('_'))]).get_names()))
        players = \
            set(map(lambda a: a[0], self._engine.ground_all(self._kb, queries=[Term('role',Var('_'))]).get_names()))
        self._step = [i.args[0].args[0].value for i in initialState if i.args[0].functor == 'step'][0]
        playerWorldState = {}

        for playerNum in map(lambda a: a.args[0], players):
            self._playerList.append(playerNum)
            knowledge = map(lambda a: Term('thinks', playerNum, a.args[0]), initialState)
            playerPreds = initialState.union(set(knowledge))
            #Each player starts with a single initial world
            if playerNum == self._randomIdentifier:
                #Random Specific world has no thinks predicates
                playerWorldState[playerNum] = [RandomWorld(self._engine, self._baseModelFile, self._step, 1, initialState, playerNum)]
            else:
                playerWorldState[playerNum] = [World(self._engine, self._baseModelFile, self._step, 1, playerPreds, playerNum)]

        return playerWorldState

    def applyActionsToModelAndUpdate(self):
        if (None in self._moveList.values()):
            raise "Error: Must have submitted moves for all players before proceeding"
        knowsSet = set()
        for i in [_ for _ in self._playerList if _ != self._randomIdentifier]:
            newWorlds = set()
            for world in self._playerWorlds[i]:
                newWorlds = newWorlds.union(world.getSuccessorWorlds(self._moveList))
            self._playerWorlds[i] = self._normaliseProbability(newWorlds)
            #Find knowledge that is known across every state, this will derive the pknows predicate
            res = [k for (k,v) in self.query(i,Var('_')).items() if v == 1]
            for p in res:
                knowsSet.add(Term('knows', p.args[0], p.args[1]))      
        
        #Extra case, should only be one world in the random players collection
        for w in self._playerWorlds[self._randomIdentifier]:
            self._playerWorlds[self._randomIdentifier] = set(w.getSuccessorWorlds(self._moveList))

        for i in self._playerList:
            for w in self._playerWorlds[i]:
                for p in knowsSet:
                    w._preds.add(p)
                    w._kb += p
            #Add all pknows predicates to all worlds
        
        if len([(k,v) for (k,v) in self._rawQuery(\
             self._randomIdentifier, Term('terminal')).items() if v > 0]) > 0:
            
            self.terminal = True
        else:
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
    main_loop(model)

#Test function to demonstrate playing monty hall with the model
def playGuessing():
    model = GDLIIIProblogRep('guessinfix.gdliii')
    main_loop(model)

def main_loop(model):
    while(not model.terminal):
        playerMoves = tuple(model.getLegalMovesForPlayer(Constant(1)))
        randomMoves = tuple(model.getLegalMovesForPlayer(Constant(0)))
        model.submitAction(choice(playerMoves), Constant(1))
        model.submitAction(choice(randomMoves), Constant(0))
        model.applyActionsToModelAndUpdate()
        #For Monty Hall
        print(model.query(Constant(1), Term('car', Var('_'))))
        #For guessing game
        #print(model.query(Constant(1), Term('num', Var('_'))))
if __name__ == "__main__":
    playMonty()
    #playGuessing()
