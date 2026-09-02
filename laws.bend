# The laws. The human states them; cert.bend must prove them.

import Base
import ./main.bend as Game

# CLAIM:
# For any sequence of moves,
# applying it to the initial
# game state doesn't result
# in victory.
assert winning_is_a_bug:
  forall moves: List<Game.Move>
  {Game.is_won(Game.apply(Game.init(), moves)) == False{} : Bool}
