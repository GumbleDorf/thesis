from GDLIIIEngine import GDLIIIEngine
from internal.GDLIIIParser import File_Format
from problog.logic import Term, Constant,Var, Clause
from random import choice

# We can figure this out from the GDLEngine too
PLAYER_NAME = 'candidate'

def main():
    mod = GDLIIIEngine('./examples/muddy.gdliii', File_Format.PREFIX)
    step = 0
    while not mod.is_terminal():
        moves = mod.get_legal_moves()
        rmove = choice(moves['random'])
        #all noops for players
        mov = {'ann': moves['ann'][0], \
            'bob':moves['bob'][0],\
            'random':rmove}
        print(f"Step {step}: {mov}")
        mod.set_actions(mov)
        mod.update_step()
        step += 1

if __name__ == "__main__":
    main()