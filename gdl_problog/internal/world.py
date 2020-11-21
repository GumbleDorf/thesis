from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
import itertools
from functools import reduce
from uuid import uuid4
from operator import mul
class World(object):
    def __init__(self, engine, model, step, prob, preds, player, tokens=None, moves_id=None):
        #Set of predicates required to generate this world from the base file
        self._preds = preds
        self._engine = engine
        self._player = player
        self._baseModel = model
        self._kb = self._engine.prepare(self._baseModel)
        self.resulting_moves = moves_id
        for i in preds:
            self._kb += i
        
        self._state = None
        self._prob = prob
        self._step = step
        self._tokens = tokens
    #Get all possible successor worlds, but do not eliminate invalid worlds from knowledge token invalidation
    #This is duplicated, refactor sometime
    def get_speculative_worlds(self, takenMoves):
        potentialMovesByOthers = {}
        tempKb = self.copy()
        for i in takenMoves.keys():
            if i == self._player:
                tempKb += Term('does', i, takenMoves[i].args[1])
                potentialMovesByOthers[i] = {
                    Term('thinks_move', self._player,
                        Term('does', i, takenMoves[i].args[1])): 1
                }
            else:
                potentialMovesByOthers[i] = self.query(\
                    [Term('thinks_move', self._player, \
                        Term('does', i, Var('_')))], kb=tempKb, prob_override=1)
        potentialMoveSequences = \
            self._processMoveSequences(\
                itertools.product(*[[(key, val) for (key, val) in potentialMovesByOthers[key].items()] \
                    for key in potentialMovesByOthers.keys()]))

        successorWorlds = []
        for moves, seqProb in potentialMoveSequences:
            copyKb = tempKb.extend()
            for m in moves:
                copyKb += m
            nextState = map(lambda a: Term('ptrue', a.args[0]) if a.args[0].functor != "thinks" else a.args[0],\
                self.query([Term('next', Var('_'))], kb=copyKb).keys())
            potentialWorld = World(self._engine, self._baseModel, self._step + 1,\
                seqProb*self._prob, set(nextState), self._player,None,)
            successorWorlds.append(potentialWorld)
        return set(successorWorlds)

    #Assumption is that this world is discarded after this function is called
    #If simulation is called
    def getSuccessorWorlds(self, takenMoves):
        potentialMovesByOthers = {}
        tempKb = self.copy()
        for i in takenMoves.keys():
            tempKb += Term('does', i, takenMoves[i].args[1])
            if i == self._player:
                potentialMovesByOthers[i] = {
                    Term('thinks_move', self._player,
                        Term('does', i, takenMoves[i].args[1])): 1
                }
            else:
                potentialMovesByOthers[i] = self.query(\
                    [Term('thinks_move', self._player, \
                        Term('does', i, Var('_')))], kb=tempKb)
        potentialMoveSequences = \
            self._processMoveSequences(\
                itertools.product(*[[(key, val) for (key, val) in potentialMovesByOthers[key].items()] \
                    for key in potentialMovesByOthers.keys()]))
        tkquery = self.query([Term('sees', self._player, Var('_'))], kb=tempKb).keys()
        tokens = list(map(lambda a: str(a.args[1]),tkquery)) 
        tokens.sort()
        tkkey = "".join(tokens)
        worlds = {}
        for moves, seqProb in potentialMoveSequences:
            copyKb = tempKb.extend()
            for m in moves:
                copyKb += m
            potentialTokens = set(map(lambda a: a.args[1], self.query([Term('thinks', self._player, \
                Term('sees', self._player, Var('_')))],kb=copyKb).keys()))
            move_id = list(map(lambda a: str(a.args[1]),moves))
            move_id.sort()
            move_id = "".join(move_id)
            ptklist = list(map(lambda a: str(a.args[1]),potentialTokens))
            ptklist.sort()
            ptkkey = "".join(ptklist)
            nextState = map(lambda a: Term('ptrue', a.args[0]) if a.args[0].functor != "thinks" else a.args[0],\
                self.query([Term('next', Var('_'))], kb=copyKb).keys())
            move_id = list(map(lambda a: str(a.args[1]),moves))
            move_id.sort()
            move_id = "".join(move_id)
            ptklist = list(map(lambda a: str(a.args[1]),potentialTokens))
            ptklist.sort()
            ptkkey = "".join(ptklist)
            potentialWorld = World(self._engine, self._baseModel, self._step + 1,\
                seqProb*self._prob, set(nextState), self._player, ptkkey, move_id)
            if ptkkey not in worlds.keys():
                worlds[ptkkey] = set()
            worlds[ptkkey].add(potentialWorld)

        return (worlds, tkkey)

    # Extract the action out of the knowledge predicate and cumulatively multiply action probabilities to get total sequence probability
    def _processMoveSequences(self, moveSequences):
        return list(map(\
            lambda seq: (set(map(lambda a: Term('thinks', a[0].args[0], a[0].args[1]),seq)), \
                reduce(mul, map(lambda a: a[1], seq))), moveSequences))

    def query(self, queries, kb=None, prob_override=None):
        if kb is None:
            copyDb = self.copy()
        else:
            copyDb = kb.extend()
        if prob_override==None:
            prob_override = self._prob
        for query in queries:
            copyDb += Term('query', query)

        ret = get_evaluatable().create_from(copyDb).evaluate()
        for (k,v) in ret.items():
            ret[k] = v*prob_override
        return ret

    #Get legal moves from the perspective of the world player on the moves of a player
    def getLegalMoves(self, playerOfLegalMove):
        return set(map(lambda a: a.args[2],
            self.query([Term('thinks', self._player, Term('legal', playerOfLegalMove, Var('_')))]).keys()\
        ))
    
    def copy(self):
        return self._kb.extend()