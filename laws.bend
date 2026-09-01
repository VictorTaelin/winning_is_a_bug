# Winning Is A Bug -- the laws.
#
# This file is the human's half of the codebase: the claims, and nothing
# else. It imports the game and states what must be true about it; it
# proves nothing and computes nothing. The proofs live in cert.bend,
# which is written and rewritten by an AI and must fill every assert
# below -- Bend rejects an unfilled assert, so the moment a law stops
# holding, the book stops checking. The human edits the laws; the AI can
# do anything it wants on the other side of the wall, except lie.

import Base
import ./main.bend as Game

# LAW: winning is a bug.
#
# For every list of player actions -- every walk, every wrap around the
# torus, every grab, in every order, of any length -- running the game
# from its initial state leaves `won` False. The flag is right there in
# the room. The room has only two walls. Try anyway: if you ever see the
# win screen, file a bug against the type checker.

assert winning_is_a_bug:
  forall t: List<Game.Act>
  {Game.won(Game.run(t, Game.init())) == False{} : Bool}
