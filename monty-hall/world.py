from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
import itertools
from functools import reduce
from operator import mul
class World(object):
    def __init__(self, engine, model, step, prob, preds, player, tokens=None):
        #Set of predicates required to generate this world from the base file
        self._preds = preds

        self._engine = engine
        self._player = player
        self._baseModel = model
        self._kb = self._engine.prepare(self._baseModel)

        for i in preds:
            self._kb += i
        
        self._state = None
        self._prob = prob
        self._step = step
        self._tokens = tokens

    #Assumption is that this world is discarded after this function is called
    def getSuccessorWorlds(self, takenMoves):
        potentialMovesByOthers = {}
        for i in takenMoves.keys():
            self._kb += Term('does', i, takenMoves[i].args[1])
            if i == self._player:
                potentialMovesByOthers[i] = {
                    Term('knowsMove', self._player, Term('step', Constant(self._step)),
                        Term('does', i, takenMoves[i].args[1])): 1
                }
            else:
                potentialMovesByOthers[i] = self.query(\
                    [Term('knowsMove', self._player, Term('step', Constant(self._step)), \
                        Term('does', i, Var('_')))])
        
        potentialMoveSequences = \
            self._processMoveSequences(\
                itertools.product(*[[(key, val) for (key, val) in potentialMovesByOthers[key].items()] \
                    for key in potentialMovesByOthers.keys()]))

        tokens = list(self.query([Term('sees', self._player, Var('_'))]).keys())
        successorWorlds = []
        for moves, seqProb in potentialMoveSequences:
            copyKb = self.copy()
            for m in moves:
                copyKb += m
            potentialTokens = list(map(lambda a: a.args[2], self.query([Term('knows', self._player, \
                Term('step', Constant(self._step)), Term('sees', self._player, Var('_')))],kb=copyKb).keys()))
            nextState = map(lambda a: Term('ptrue', a.args[0]),\
                self.query([Term('next', Var('_'))], kb=copyKb).keys())
            nextPlayerKnowledge = self.query([Term('knows', self._player, \
                Term('step', Constant(self._step+1)), Var('_'))], kb=copyKb).keys()

            potentialWorld = World(self._engine, self._baseModel, self._step + 1,\
                seqProb*self._prob, set(nextState).union(nextPlayerKnowledge), self._player, tokens)
            if tokens == potentialTokens:
                successorWorlds.append(potentialWorld)

        return set(successorWorlds)

    # Extract the action out of the knowledge predicate and cumulatively multiply action probabilities to get total sequence probability
    def _processMoveSequences(self, moveSequences):
        return list(map(\
            lambda seq: (set(map(lambda a: Term('knows', a[0].args[0], a[0].args[1], a[0].args[2]),seq)), \
                reduce(mul, map(lambda a: a[1], seq))), moveSequences))

    def _normaliseProbabilities(self, world):
        pass

    def query(self, queries, kb=None):
        if kb is None:
            copyDb = self.copy()
        else:
            copyDb = kb.extend()
        for query in queries:
            copyDb += Term('query', query)
        return get_evaluatable().create_from(copyDb).evaluate()

    def queryFuture(self, queries):
        copyKb = self.copy()
        copyKb += Clause(Term('knows', Var('X'), Var('Y'), Var('Z')), Term('knowsMove', Var('X'), Var('Y'), Var('Z')))
        return self.query(queries, kb=copyKb)

    def getLegalMoves(self, playerOfLegalMove):
        return set(map(lambda a: a.args[2],
            self.query([Term('knows', self._player, Term('step', Constant(self._step)), Term('legal', playerOfLegalMove, Var('_')))]).keys()\
        ))
        

    def copy(self):
        return self._kb.extend()