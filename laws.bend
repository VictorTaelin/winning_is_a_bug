# Winning Is A Bug -- the laws.
#
# This file is the human's half of the codebase. It holds types and
# asserts -- specs -- and nothing else: no algorithm, no proof. The other
# half is main.bend, written and rewritten by an AI, which imports this
# file and must FILL every assert below. Bend makes the contract hard:
# an unfilled assert is an error outside base, so the moment main.bend
# stops proving a law, the book stops checking. The human edits the
# laws; the AI can do anything it wants on the other side of the wall,
# except lie.

import Base

# The player's inputs: a step in one of four directions, or a grab.

type Act is Data:
  Up{}
  Down{}
  Left{}
  Right{}
  Grab{}

# The whole game state: the player's cell, and whether the game is won.

type Game is Data:
  Game{x: Nat, y: Nat, won: Bool}

# The game, as three functions: where it starts, how a list of actions
# drives it, and what winning means.

assert init:
  Game

assert run:
  forall t: List<Act>
  forall g: Game
  Game

assert won:
  forall g: Game
  Bool

# LAW: winning is a bug.
#
# For every list of player actions -- every walk, every wrap around the
# torus, every grab, in every order, of any length -- running the game
# from its initial state leaves `won` False. The flag is right there in
# the room. The room has only two walls. Try anyway: if you ever see the
# win screen, file a bug against the type checker.

assert winning_is_a_bug:
  forall t: List<Act>
  {won(run(t, init())) == False{} : Bool}
