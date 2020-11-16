from internal.GDLIIIProblogRep import GDLIIIProblogRep
from internal.GDLIIIParser import File_Format
from problog.logic import Term, Constant,Var, Clause
from random import choice

class GDLIIIEngine(object):
    def __init__(self, file_name, fformat):
        self._cur_step = 0
        self._gdl_rep = GDLIIIProblogRep(file_name, fformat)
        self._player_map = self._gdl_rep._model.player_map
        self.player_names = list(self._player_map.keys())
    #Must be called when inserting player name into a query clause
    def player_to_id(self, player):
        return self._player_map[player]
    # Make a query at the current step, alternatively, make a query to a future step using only currently known information
    # Query is made from the perspective of player names in player parameter
    # Returns a list of pairs, with probability in index 0 and the corresponding predicate in index 1
    def query(self, player, query, step=0):
        if (type(step) != int) or (step < 0):
            raise Exception("Expected step to be None or integer >= cur_step")
        if player not in self.player_names:
            raise Exception("{} is an undefined role".format(player))
        if player == 'random':
            raise Exception("Random player does not track knowledge state")
        return sorted([(prob,pred.args[1]) for (pred, prob) in self._gdl_rep.query(Constant(self._player_map[player]), query, step).items()])
    # Get moves for every player, or alternatively, specify a player and only recieve current legal moves for them
    def get_legal_moves(self, player=None):
        if player is None:
            action_dict = {}
            for i in self.player_names:
                action_dict[i] = [i.args[1] for i in self._gdl_rep.getLegalMovesForPlayer(self._player_map[i]).keys()]
            return action_dict
        else:
            return [i.args[1] for i in self._gdl_rep.getLegalMovesForPlayer(self._player_map[player]).keys()]
    # Pass in a dict of actions for each player
    # Alternatively, pass in a dict containing only a subset of player actions
    def set_actions(self, moves={}):
        for (player, action) in moves.items():
            if player not in self.player_names:
                raise Exception("{} is an undefined role".format(player))
            self._gdl_rep.submitAction(Term('legal', Constant(self._player_map[player]), action), self._player_map[player])
    # Undo all actions and go back a step
    # Optionally, set increment to a value greater than 1 to undo multiple steps
    def undo_step(self, increment=1):
        if self._cur_step == 0:
            raise Exception("Cannot undo a game with 0 actions made")
        if type(increment) != int or increment < 1 or increment > self._cur_step:
            raise Exception("Expected increment to be an integer >= 1")
        self._gdl_rep.undo(increment)
    # Process the actions in the queue and move to the next step
    # Can only be called if every player has a valid move
    def update_step(self):
        if self.is_terminal():
            raise Exception("Cannot continue to next step, current state is terminal")
        if self._gdl_rep.getMoveList()[self._gdl_rep._randomIdentifier] is None:
            self._gdl_rep.submitAction(choice(tuple(self._gdl_rep.getLegalMovesForPlayer(self._gdl_rep._randomIdentifier))), self._gdl_rep._randomIdentifier)
        self._gdl_rep.applyActionsToModelAndUpdate()
        self._cur_step +=1

    def is_terminal(self):
        return self._gdl_rep.terminal


if __name__ == "__main__":
    mod = GDLIIIEngine('./examples/montyhall.gdliii', File_Format.INFIX)
    print(mod.player_names)
    print(mod.get_legal_moves())
    mod.set_actions({'candidate': mod.get_legal_moves('candidate')[0]})
    mod.update_step()
    print(mod.get_legal_moves())
    mod.set_actions({'candidate': mod.get_legal_moves('candidate')[0]})
    mod.update_step()
    print(mod.is_terminal())
    print(mod.query('candidate', Term('car', Var("_")), 0))
    print(mod.query('candidate', Term('car', Var("_")), 1))
    mod.set_actions({'candidate': mod.get_legal_moves('candidate')[0]})
    mod.update_step()
    print(mod.is_terminal())
    print(mod.query('candidate', Term('car', Var("_"))))
