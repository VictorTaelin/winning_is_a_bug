# The laws. The human states them; cert.bend must prove them.

import Base
import ./main.bend as Game

# No list of actions ever wins the game.

assert winning_is_a_bug:
  forall t: List<Game.Act>
  {Game.won(Game.run(t, Game.init())) == False{} : Bool}
