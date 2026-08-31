# Winning Is A Bug -- the laws.
#
# This file is the human's half of the codebase. It states what must be
# true; it proves nothing and computes nothing. The other half is
# main.bend -- the game, its algorithms, and the proofs -- and that half
# is written and rewritten by an AI. The contract between the two halves
# is this file: each law below names a proof that main.bend must supply,
# and `bend laws.bend` fails the moment any of them breaks. The human
# edits the laws; the AI can do anything it wants on the other side of
# the wall, except lie.

import ./main.bend as Game

# LAW: winning is a bug.
#
# For every list of player actions -- every walk, every wrap around the
# torus, every grab, in every order, of any length -- running the game
# from its initial state leaves `won` False. The flag is right there in
# the room. The room has only two walls. Try anyway: if you ever see the
# win screen, file a bug against the type checker.

def winning_is_a_bug(t: List<Game.Act>)
  -> {Game.won(Game.run(t, Game.init())) == False{} : Bool}:
  Game.winning_proof(t)
