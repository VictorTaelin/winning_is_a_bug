# Winning Is A Bug
# ================
#
# A tiny game whose whole point is a theorem. The map is a torus: walk off
# one edge and you come back on the opposite one. A room sits on the
# top-left corner, the flag sits inside it, and two walls seal it -- the
# room's other two walls exist too, you just see them on the far edges of
# the screen, because that is where the wrap puts them. You move, you grab,
# and you never win: `winning_is_a_bug` (the theorem this file exists to
# carry) will prove that no sequence of actions sets `won`.
#
# The file is the whole game. `main` prints the map (the build script reads
# it from there, so the .bend source is the single author of the level) and
# runs a short walk as a self-test. The browser front end drives `run` one
# action at a time and only draws the state it gets back.

import Base

# Act
# ---
# One player input: a step in one of four directions, or a grab. Grabbing
# wins if (and only if) the player stands on the flag.

type Act is Data:
  Up{}
  Down{}
  Left{}
  Right{}
  Grab{}

# Game
# ----
# The whole game state: the player's cell, and whether the game was won.

type Game is Data:
  Game{x: Nat, y: Nat, won: Bool}

# Map
# ---
# The level, as pure functions. The grid is map_w by map_h, wrapping on
# both axes. The room is the top-left corner: its east wall is the column
# x = room_w (down to y = room_h), its south wall is the row y = room_h
# (up to x = room_w). Its north and west walls are the same two strips
# seen through the wrap: they guard the bottom-left and top-right edges,
# because on a torus that IS the other side of the room.

assert map_w:
  Nat

def map_w():
  14n

assert map_h:
  Nat

def map_h():
  10n

assert room_w:
  Nat

def room_w():
  4n

assert room_h:
  Nat

def room_h():
  3n

assert flag_x:
  Nat

def flag_x():
  1n

assert flag_y:
  Nat

def flag_y():
  1n

assert start_x:
  Nat

def start_x():
  9n

assert start_y:
  Nat

def start_y():
  6n

assert nat_eq:
  forall a: Nat
  forall b: Nat
  Bool

def nat_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert nat_le:
  forall a: Nat
  forall b: Nat
  Bool

def nat_le(a, b):
  Cmp.is_le(Nat.cmp(a, b))

assert wall:
  forall +x: Nat
  forall +y: Nat
  Bool

def wall(x, y):
  east  = nat_eq(x, room_w()) && nat_le(y, room_h())
  south = nat_le(x, room_w()) && nat_eq(y, room_h())
  north = nat_le(x, room_w()) && nat_eq(y, Nat.sub(map_h(), 1n))
  west  = nat_eq(x, Nat.sub(map_w(), 1n)) && nat_le(y, room_h())
  (east || south) || (north || west)

# Step
# ----
# One action against one state. Each warp_* takes one step on one axis,
# wrapping at the edge; move commits the walk unless a wall stands on the
# target cell; pick is the branch as a function (both arms ride in, the
# loser is dropped -- dropping is free).

assert pick:
  forall -A: Type
  forall c: Bool
  forall a: A
  forall b: A
  A

def pick(A, c, a, b):
  match c:
    case True{}:
      a
    case False{}:
      b

assert warp_up:
  forall y: Nat
  Nat

def warp_up(y):
  match y:
    case 0n:
      Nat.sub(map_h(), 1n)
    case 1n+p:
      p

assert warp_down:
  forall +y: Nat
  Nat

def warp_down(y):
  pick(Nat, nat_eq(1n+y, map_h()), 0n, 1n+y)

assert warp_left:
  forall x: Nat
  Nat

def warp_left(x):
  match x:
    case 0n:
      Nat.sub(map_w(), 1n)
    case 1n+p:
      p

assert warp_right:
  forall +x: Nat
  Nat

def warp_right(x):
  pick(Nat, nat_eq(1n+x, map_w()), 0n, 1n+x)

assert move:
  forall +tx: Nat
  forall +ty: Nat
  forall g: Game
  Game

def move(tx, ty, g):
  Game{x, y, w0} = g
  +w = w0
  pick(Game, wall(tx, ty), Game{x, y, w}, Game{tx, ty, w})

assert step:
  forall a: Act
  forall g: Game
  Game

def step(a, g):
  match a:
    case Up{}:
      Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(x, warp_up(y), Game{x, y, w})
    case Down{}:
      Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(x, warp_down(y), Game{x, y, w})
    case Left{}:
      Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(warp_left(x), y, Game{x, y, w})
    case Right{}:
      Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(warp_right(x), y, Game{x, y, w})
    case Grab{}:
      Game{x0, y0, w} = g
      +x = x0
      +y = y0
      Game{x, y, w || (nat_eq(x, flag_x()) && nat_eq(y, flag_y()))}

# Run
# ---
# The game, whole: fold a list of actions over a state. This is the one
# entry the front end calls, and the function the theorem will quantify
# over: for every list t, won(run(t, init())) is False.

assert init:
  Game

def init():
  Game{start_x(), start_y(), False{}}

assert run:
  forall t: List<Act>
  forall g: Game
  Game

def run(t, g):
  match t:
    case Nil{}:
      g
    case Con{a, as}:
      run(as, step(a, g))

assert won:
  forall g: Game
  Bool

def won(g):
  Game{x, y, w} = g
  w

# Show
# ----
# The map, printed: '#' wall, 'F' flag, 'P' the starting cell, '.' floor.
# The build script parses this exact grid out of the compiled program's
# stdout, so the level is defined once, here.

assert cell:
  forall +x: Nat
  forall +y: Nat
  String

def cell(x, y):
  is_flag  = nat_eq(x, flag_x()) && nat_eq(y, flag_y())
  is_start = nat_eq(x, start_x()) && nat_eq(y, start_y())
  pick(String, wall(x, y), "#",
    pick(String, is_flag, "F",
      pick(String, is_start, "P", ".")))

assert row:
  forall x: Nat
  forall +y: Nat
  String

def row(x, y):
  match x:
    case 0n:
      cell(0n, y)
    case 1n+p0:
      +p = p0
      row(p, y) ++ cell(1n+p, y)

assert grid:
  forall y: Nat
  String

def grid(y):
  match y:
    case 0n:
      row(Nat.sub(map_w(), 1n), 0n)
    case 1n+p0:
      +p = p0
      grid(p) ++ "\n" ++ row(Nat.sub(map_w(), 1n), 1n+p)

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    u : Unit <- IO.print(grid(Nat.sub(map_h(), 1n)))
    IO.print(pick(String, won(run([Left{}, Left{}, Up{}, Grab{}], init())),
      "WON (this line is unreachable)", "still not won"))
