from GDLIIIEngine import GDLIIIEngine
from internal.GDLIIIParser import File_Format
from problog.logic import Term, Constant,Var, Clause
from random import choice

# We can figure this out from the GDLEngine too
PLAYER_NAME = 'candidate'

def main():
    mod = GDLIIIEngine('./examples/muddy.gdliii', File_Format.PREFIX)
    moves = mod.get_legal_moves()
    print(moves)
    #all noops for players
    mod.set_actions({'ann': moves['ann'][0], \
        'bob':moves['bob'][0],\
        'random':moves['random'][0]})
    mod.update_step()
    moves = mod.get_legal_moves()
    print(mod.get_legal_moves())
    mod.set_actions({'ann': moves['ann'][0], \
        'bob':moves['bob'][0],\
        'random':moves['random'][0]})
    mod.update_step()
    moves = mod.get_legal_moves()
    print(mod.get_legal_moves())
    mod.set_actions({'ann': moves['ann'][0], \
        'bob':moves['bob'][0],\
        'random':moves['random'][0]})
    mod.update_step()
    print(mod.get_legal_moves())


if __name__ == "__main__":
    main()