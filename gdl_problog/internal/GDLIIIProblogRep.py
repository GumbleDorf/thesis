from problog.program import PrologFile, PrologString,LogicProgram
from problog.engine import DefaultEngine, ClauseDB
from problog.logic import Term, Constant,Var, Clause
from problog import get_evaluatable
from random import choice
from itertools import product
from copy import deepcopy
from internal.world import World
from internal.randomWorld import RandomWorld
from internal.GDLIIIParser import GDLIIIParser, File_Format

NO_SEEN_TOKENS_KEY = '-2'

class GameData(object):
    def __init__(self, players, random_id):
        self.players = players
        self.random_id = random_id

class GDLNode(object):
    def __init__(self, worlds: dict, game_data: GameData, parent = None):
        self.parent = parent
        self.worlds = worlds
        self.game_data = game_data
        self.successors = {}
        self.legal_moves = self._generate_legal_moves()

    def _hash_actions(self, actions):
        return "".join(sorted(list(map(str,actions.items()))))

    def get_next_node(self, actions):
        key = self._hash_actions(actions)
        if key not in self.successors.keys():
            self.successors[key] = self._generate_successor_worlds(actions)
        return self.successors[key]

    def set_next_node(self,node, actions):
        key = self._hash_actions(actions)
        self.successors[key] = node

    def raw_query(self, player, query, worlds=None):
        if worlds is None:
            worlds = self.worlds
        initialResults = []
        #Assumption: Sum of all probabilities of worlds == 1
        for world in worlds[player]:
            initialResults.append(world.query([query]))
        keys = set([i for d in initialResults for i in d.keys()])
        queryResults = {}
        for k in keys:
            queryResults[k] = 0
            for d in initialResults:
                if k in d.keys():
                    queryResults[k] += d[k]
        return queryResults

    def get_legal_moves(self):
        return self.legal_moves

    def _generate_legal_moves(self):
        legalMoves = {}
        for player in self.worlds.keys():
            legalMoves[player] = {}
            for world in self.worlds[player]:
                legalMoves[player] = world.query([Term('legal', player, Var('_'))])
                break
        return legalMoves

    #Returns worlds with only information relevant to the player
    def generate_speculative_worlds(self, player, actions):
        knowsSet = set()
        total_new_worlds = {}
        newWorlds = set()
        for world in self.worlds[player]:
            (wd, truekey) = world.getSuccessorWorlds(actions)
            newWorlds = newWorlds.union(wd[truekey])
        total_new_worlds[player] = self._normaliseProbability(newWorlds)
        #Find knowledge that is known across every state, this will derive the knows predicate
        res = [k for (k,v) in self.raw_query(player, Term('thinks', player, Var('_')), total_new_worlds).items() if v == 1]
        for p in res:
            t = Term('knows', p.args[0], p.args[1])
            knowsSet.add(t)
            knowsSet.add(Term('thinks', player, t))
        for w in total_new_worlds[player]:
            for p in knowsSet:
                w._preds.add(p)
                w._kb += p
        return GDLNode(total_new_worlds, self.game_data, self)

    def _generate_successor_worlds(self, actions):
        total_new_worlds = {}
        players_less_random = [_ for _ in self.game_data.players if _ != self.game_data.random_id]
        all_worlds = {}
        knowsSet = set()
        for i in players_less_random:
            all_worlds[i] = {}
            newWorlds = set()
            truekey = None
            for world in self.worlds[i]:
                (wd,truekey) = world.getSuccessorWorlds(actions)
                try:
                    newWorlds = newWorlds.union(wd[truekey])
                except:
                    pass
                for m in wd.keys():
                    if m not in all_worlds[i].keys():
                        all_worlds[i][m] = set()
                    all_worlds[i][m] = all_worlds[i][m].union(wd[m])
            total_new_worlds[i] = self._normaliseProbability(newWorlds)
            #Find knowledge that is known across every state, this will derive the knows predicate
            res = [k for (k,v) in self.raw_query(i, Term('thinks', i, Var('_')), total_new_worlds).items() if v == 1 and k.args[1].functor != "legal"]
            for p in res:
                t = Term('knows', p.args[0], p.args[1])
                knowsSet.add(t)
            for w in total_new_worlds[i]:
                for p in knowsSet:
                    w._preds.add(Term('thinks', i, p))
                    w._kb += Term('thinks', i, p)
        
        for i in players_less_random:
            for w in total_new_worlds[i]:
                for p in knowsSet:
                    w._preds.add(p)
                    w._kb += p

        for i in players_less_random:
            #Get knowledge in every other state
            for m in all_worlds[i].keys():
                if m != truekey:
                    knows = self.get_knows_for_worlds(all_worlds[i][m])
                    for p in knows:
                        for wm in all_worlds[i][m]:
                            wm._preds.add(Term('knows', i,p))


        #Generate Inferred knowledge
        kvworlds = {}
        for i in players_less_random:
            for w in total_new_worlds[i]:
                kvworlds[w] = [Term('thinks',i,p) for p in self.generate_inferred_knowledge(w,all_worlds)]

        for (w,k) in kvworlds.items():
            for p in k:
                w._preds.add(p)
                w._kb += p
        knowsSet2 = set()
        #Generate new legal moves
        for i in players_less_random:
            res = [k for (k,v) in self.raw_query(i, Term('thinks', i, Var('_')), total_new_worlds).items() if v == 1 and k.args[1].functor == "legal"]
            for q in res:
                knowsSet2.add(Term('knows', i, q.args[1]))
        for i in players_less_random:
            for w in total_new_worlds[i]:
                for p in knowsSet2:
                    w._preds.add(p)
                    w._kb += Term(p)


        #Extra case, should only be one world in the random players collection
        if self.game_data.random_id in self.worlds.keys():
            for w in self.worlds[self.game_data.random_id]:
                total_new_worlds[self.game_data.random_id] = set(w.getSuccessorWorlds(actions))
                for w1 in total_new_worlds[self.game_data.random_id]:
                    for p1 in knowsSet:
                        w1._preds.add(p1)
                        w1._kb += p1
                    for p2 in knowsSet2:
                        w1._preds.add(p2)
                        w1._kb += p2
                break
        return GDLNode(total_new_worlds, self.game_data, self)

    def _normaliseProbability(self,worlds):
        totalprob = 0
        for w in worlds:
            totalprob += w._prob
        for w in worlds:
            w._prob = w._prob / totalprob
        return worlds
    
    def generate_inferred_knowledge(self,world,all_worlds):
        for i in all_worlds.keys():
            if i == world._player:
                continue
            for j in all_worlds[i].keys():
                same_token = None
                for w in all_worlds[i][j]:
                    if same_token is None and self.state(w) == self.state(world):
                        same_token = j
                        preds = set([p for p in w._preds if p.functor == "knows" and p.args[0] == i and p.args[1].functor != "legal"])
                        return preds
        return set()

    def state(self, world):
        ppreds = set()
        for p in world._preds:
            if p.functor == "thinks" and p.args[0] == world._player and p.args[1].functor != "knows":
                ppreds.add(p.args[1])
        return ppreds

    def get_knows_for_worlds(self, worlds):
        preds = set()
        for w in worlds:
            dis_set = set()
            for p in w.query([Term('thinks', w._player, Var('_'))],prob_override=1):
                if p.functor == "thinks":
                    tp = p.args[1]
                    if tp.functor != "knows":
                        dis_set.add(tp)
            
            if len(preds) == 0:
                preds = dis_set
            else:
                preds &= dis_set
        return preds


#This is just a preliminary program to solve Monty Hall, not generalised yet.
class GDLIIIProblogRep(object):
    def __init__(self, program, fformat):
        #GlobalEngine
        self._engine = DefaultEngine()
        gdl_parser = GDLIIIParser()
        self._model = gdl_parser.output_model(program, fformat)
        self._baseModelFile = self._model.as_problog()
        self._playerList = []
        self._randomIdentifier = Constant(0) #Hardcoded to give the random player a specific constant id as we apply some special rules to the random player
        worlds = self._initialiseKB()
        self._cur_node = GDLNode(worlds, GameData(self._playerList, self._randomIdentifier))
        self._moveList = dict([(i,None) for i in self._playerList])
        self.terminal = False

    def getMoveList(self):
        return self._moveList

    def undo(self, increment=1):
        for _ in range(increment):
            self._cur_node = self._cur_node.parent
        self._moveList = dict([(i,None) for i in self._playerList])
        if self.terminal:
            self.terminal = False

    def getLegalMovesForPlayer(self, player):
        return self._cur_node.legal_moves[player]

    def _resetKnowledgeBase(self):
        self._kb = self._engine.prepare(self._baseModelFile)

    def getPlayersPossibleWorlds(self, player):
        return self._cur_node.worlds[player]


    #Assumption, term contains a single argument
    def extractSingleArg(self,nArg, term):
        return term.args[nArg]

    #Recommended to never call this function with step > 1 as it will likely take a long time, exponential time complexity for values of step > 0.
    def query(self, player, query, step=0):
        if step == 0:
            return self._cur_node.raw_query(player, Term('thinks', player, query))
        else:
            world_set = set([self._cur_node])
            for _ in range(step):
                #Create set of all possible move sequences from perspective of player
                action_set = set()
                for world in world_set:
                    action_set = action_set.union(set([i for i in world.get_legal_moves()[player].keys()]))
                legal_moves_seqs = [{k:(None if k != player else a) for k in self._playerList} for a in action_set]
                #Generate possible (but not always valid) successor worlds
                new_set = set()
                for world in world_set:
                    for actions in legal_moves_seqs:
                        new_set.add(world.generate_speculative_worlds(player, actions))
                world_set = new_set

            query_dict = {}
            size = len(world_set)
            for w in world_set:
                for (item,val) in w.raw_query(player, Term('thinks', player, query)).items():
                    if item in query_dict.keys():
                        query_dict[item] += val/size
                    else:
                        query_dict[item] = val/size
            return query_dict

    #Private
    def _initialiseKB(self):
        self._kb = self._engine.prepare(self._baseModelFile)
        initialState = \
            set(map(lambda a: Term('ptrue', a[0].args[0]), self._engine.ground_all(self._kb, queries=[Term('init',Var('_'))]).get_names()))
        players = \
            set(map(lambda a: a[0], self._engine.ground_all(self._kb, queries=[Term('role',Var('_'))]).get_names()))
        #Not needed, but dont care to remove right now
        self._step = 0
        playerWorldState = {}

        for playerNum in map(lambda a: a.args[0], players):
            knowledge = map(lambda a: Term('thinks', playerNum, a.args[0]), initialState)
            playerPreds = initialState.union(set(knowledge))
            self._playerList.append(playerNum)
            #Each player starts with a single initial world
            if playerNum == self._randomIdentifier:
                #Random Specific world has no thinks predicates
                playerWorldState[playerNum] = [RandomWorld(self._engine, self._baseModelFile, self._step, 1, initialState, playerNum)]
            else:
                playerWorldState[playerNum] = [World(self._engine, self._baseModelFile, self._step, 1, playerPreds, playerNum)]
        return playerWorldState

    def applyActionsToModelAndUpdate(self):
        if (None in self._moveList.values()):
            raise Exception("Error: Must have submitted moves for all players before proceeding")
        self._cur_node = self._cur_node.get_next_node(self._moveList)
        #Assume, there is at least one player
        if len([(k,v) for (k,v) in self._cur_node.raw_query(\
             self._playerList[0], Term('terminal')).items() if v > 0]) > 0:
            self.terminal = True

        self._step += 1
        self._moveList = dict([(i,None) for i in self._playerList])

    def submitAction(self, action, player):
        if ( action not in self.getLegalMovesForPlayer(player)):
            raise Exception("{} is not a legal action".format(action))
        self._moveList[player] = action

    

#Test function to demonstrate playing monty hall with the model
def playMonty():
    model = GDLIIIProblogRep('./examples/montyhall.gdliii', File_Format.INFIX)
    main_loop(model)

#Test function to demonstrate playing monty hall with the model
def playGuessing():
    model = GDLIIIProblogRep('./examples/guess.gdliii', File_Format.PREFIX)
    main_loop(model)

def main_loop(model):
    while(not model.terminal):
        playerMoves = tuple(model.getLegalMovesForPlayer(Constant(1)))
        randomMoves = tuple(model.getLegalMovesForPlayer(Constant(0)))
        model.submitAction(choice(playerMoves), Constant(1))
        model.submitAction(choice(randomMoves), Constant(0))
        model.applyActionsToModelAndUpdate()
        #For Monty Hall
        #print(model.query(Constant(1), Term('car', Var('_'))))
        #For guessing game
        print(model.query(Constant(1), Term('num', Var('_'))))
if __name__ == "__main__":
    #playMonty()
    playGuessing()
