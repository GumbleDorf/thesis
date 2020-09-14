from internal.world import World
from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
class RandomWorld(World):

    #Get the successor worlds of random, random does not model any knowledge
    def getSuccessorWorlds(self, takenMoves):
        copyKb = self.copy()
        for i in takenMoves.keys():
            copyKb += Term('does', i, takenMoves[i].args[1])
        #Assumption: random player never has any thinks predicates
        nextState = map(lambda a: Term('ptrue', a.args[0]),\
                self.query([Term('next', Var('_'))], kb=copyKb).keys())
        return set([RandomWorld(self._engine, self._baseModel, self._step + 1,\
                1, set(nextState), self._player, [])])

    def getLegalMoves(self, playerOfLegalMove):
        return set(map(lambda a: a.args[2],
            self.query([Term('legal', playerOfLegalMove, Var('_'))]).keys()\
        ))