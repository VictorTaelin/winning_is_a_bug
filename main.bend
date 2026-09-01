# Winning Is A Bug -- the machine.
#
# This file is the AI's side of the contract: every algorithm and every
# proof lives here. The human's side is laws.bend: types and asserts,
# which this file imports and must fill -- an unfilled assert is an
# error, so the laws hold or the book stops checking. Anything in this
# file may be rewritten at will.
#
# Three parts:
#   1. The game: a torus map, a walled room, a flag, five actions.
#   2. The show: the level as text (the front end asks `grid` for it).
#   3. The proof: `Laws.winning_is_a_bug`, by an invariant ("the player
#      stands on a safe cell") kept through every action, with the
#      finite map facts checked by computation.

import Base
import ./laws.bend as Laws

# Map
# ---

def map_w() -> Nat:
  14n

def map_h() -> Nat:
  10n

def room_w() -> Nat:
  4n

def room_h() -> Nat:
  3n

def flag_x() -> Nat:
  1n

def flag_y() -> Nat:
  1n

def start_x() -> Nat:
  9n

def start_y() -> Nat:
  6n

def nat_eq(a: Nat, b: Nat) -> Bool:
  match a:
    case 0n:
      match b:
        case 0n:
          True{}
        case 1n+q:
          False{}
    case 1n+p:
      match b:
        case 0n:
          False{}
        case 1n+q:
          nat_eq(p, q)

def nat_le(a: Nat, b: Nat) -> Bool:
  match a:
    case 0n:
      True{}
    case 1n+p:
      match b:
        case 0n:
          False{}
        case 1n+q:
          nat_le(p, q)

def wall(+x: Nat, +y: Nat) -> Bool:
  east  = nat_eq(x, room_w()) && nat_le(y, room_h())
  south = nat_le(x, room_w()) && nat_eq(y, room_h())
  north = nat_le(x, room_w()) && nat_eq(y, Nat.sub(map_h(), 1n))
  west  = nat_eq(x, Nat.sub(map_w(), 1n)) && nat_le(y, room_h())
  (east || south) || (north || west)

# Step
# ----

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def warp_up(y: Nat) -> Nat:
  match y:
    case 0n:
      Nat.sub(map_h(), 1n)
    case 1n+p:
      p

def warp_down(+y: Nat) -> Nat:
  pick(Nat, nat_eq(1n+y, map_h()), 0n, 1n+y)

def warp_left(x: Nat) -> Nat:
  match x:
    case 0n:
      Nat.sub(map_w(), 1n)
    case 1n+p:
      p

def warp_right(+x: Nat) -> Nat:
  pick(Nat, nat_eq(1n+x, map_w()), 0n, 1n+x)

def move(+tx: Nat, +ty: Nat, g: Laws.Game) -> Laws.Game:
  Laws.Game{x, y, w0} = g
  +w = w0
  pick(Laws.Game, wall(tx, ty), Laws.Game{x, y, w}, Laws.Game{tx, ty, w})

def step(a: Laws.Act, g: Laws.Game) -> Laws.Game:
  match a:
    case Laws.Up{}:
      Laws.Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(x, warp_up(y), Laws.Game{x, y, w})
    case Laws.Down{}:
      Laws.Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(x, warp_down(y), Laws.Game{x, y, w})
    case Laws.Left{}:
      Laws.Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(warp_left(x), y, Laws.Game{x, y, w})
    case Laws.Right{}:
      Laws.Game{x0, y0, w} = g
      +x = x0
      +y = y0
      move(warp_right(x), y, Laws.Game{x, y, w})
    case Laws.Grab{}:
      Laws.Game{x0, y0, w} = g
      +x = x0
      +y = y0
      Laws.Game{x, y, w || (nat_eq(x, flag_x()) && nat_eq(y, flag_y()))}

def Laws.init():
  Laws.Game{start_x(), start_y(), False{}}

def Laws.run(t, g):
  match t:
    case Nil{}:
      g
    case Con{a, as}:
      Laws.run(as, step(a, g))

def Laws.won(g):
  Laws.Game{x, y, w} = g
  w

# Show
# ----
# The map, printed: '#' wall, 'F' flag, 'P' the starting cell, '.' floor.
# The front end asks `grid` for this exact text, so the level is defined
# once, here.

def cell(+x: Nat, +y: Nat) -> String:
  is_flag  = nat_eq(x, flag_x()) && nat_eq(y, flag_y())
  is_start = nat_eq(x, start_x()) && nat_eq(y, start_y())
  pick(String, wall(x, y), "#",
    pick(String, is_flag, "F",
      pick(String, is_start, "P", ".")))

def row(x: Nat, +y: Nat) -> String:
  match x:
    case 0n:
      cell(0n, y)
    case 1n+p0:
      +p = p0
      row(p, y) ++ cell(1n+p, y)

def grid(y: Nat) -> String:
  match y:
    case 0n:
      row(Nat.sub(map_w(), 1n), 0n)
    case 1n+p0:
      +p = p0
      grid(p) ++ "\n" ++ row(Nat.sub(map_w(), 1n), 1n+p)

# Proof kit
# ---------
# Boolean reflection: T(b) is the truth of b as a type (Unit when True,
# Empty when False), so a computed check becomes a proof by conversion.
# The rest are the eliminators the affine core asks to be spelled out:
# every split is a def whose match consumes a parameter, and every
# equation is spent by one rewrite.

def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def sym(-A: Type, -a: A, -b: A, e: {a == b : A}) -> {b == a : A}:
  %e : {_ == a : A}
  {==}

def and_split(+a: Bool, -b: Bool, w: T(a && b), -P: Type,
  f: T(a) -> T(b) -> P) -> P:
  match a:
    case True{}:
      f(Unit{}, w)
    case False{}:
      Empty.absurd(P, w)

def and_intro(+a: Bool, -b: Bool, wa: T(a), wb: T(b)) -> T(a && b):
  match a:
    case True{}:
      wb
    case False{}:
      Empty.absurd(T(False{} && b), wa)

def not_elim(+a: Bool, wn: T(Bool.not(a)), wa: T(a)) -> Empty:
  match a:
    case True{}:
      wn
    case False{}:
      wa

def imp(a: Bool, b: Bool) -> Bool:
  Bool.not(a) || b

def imp_elim(+a: Bool, -b: Bool, wi: T(imp(a, b)), wa: T(a)) -> T(b):
  match a:
    case True{}:
      wi
    case False{}:
      Empty.absurd(T(b), wa)

def bool_case(+b: Bool, -P: Bool -> Type,
  t: {True{} == b : Bool} -> P(True{}),
  f: {False{} == b : Bool} -> P(False{})) -> P(b):
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

def pick_split(-A: Type, -P: A -> Type, +c: Bool, -a: A, -b: A,
  t: {True{} == c : Bool} -> P(a),
  f: {False{} == c : Bool} -> P(b)) -> P(pick(A, c, a, b)):
  match c:
    case True{}:
      t({==})
    case False{}:
      f({==})

def or_case(-A: Type, -B: Type, o: Or(A, B), -P: Type,
  f: A -> P, g: B -> P) -> P:
  match o:
    case Inl{l}:
      f(l)
    case Inr{r}:
      g(r)

def eq_sound(a: Nat, b: Nat, w: T(nat_eq(a, b))) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({0n == 1n+q : Nat}, w)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd({1n+p == 0n : Nat}, w)
        case 1n+q:
          %eq_sound(p, q, w) : {1n+p == 1n+_ : Nat}
          {==}

def le_split(a: Nat, b: Nat, w: T(nat_le(a, b)))
  -> Or(T(nat_le(1n+a, b)), {a == b : Nat}):
  match a:
    case 0n:
      match b:
        case 0n:
          Inr{{==}}
        case 1n+q:
          Inl{w}
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Or(T(nat_le(2n+p, 0n)), {1n+p == 0n : Nat}), w)
        case 1n+q:
          or_case(T(nat_le(1n+p, q)), {p == q : Nat}, le_split(p, q, w),
            Or(T(nat_le(2n+p, 1n+q)), {1n+p == 1n+q : Nat}),
            l => Inl{l},
            e => Inr{%e : {1n+p == 1n+_ : Nat}
                     {==}})

# Invariant
# ---------
# The safe cells: on the map, not inside the room, not on a wall. The
# proof shows every action keeps the player on a safe cell, and that a
# grab on a safe cell never raises the flag (the flag is in the room).
#
# The geometric heart is finite, so it is not argued -- it is computed:
# chk_all(a, 13n) enumerates every cell of the map and checks that a
# step in direction `a` from a safe cell lands on a wall or on a safe
# cell. The term evaluates to True, so its truth is Unit by conversion,
# and chk_row_at/chk_all_at index that certificate at any coordinates.

def room(+x: Nat, +y: Nat) -> Bool:
  nat_le(x, 3n) && nat_le(y, 2n)

def okpos(+x: Nat, +y: Nat) -> Bool:
  (nat_le(x, 13n) && nat_le(y, 9n))
    && (Bool.not(room(x, y)) && Bool.not(wall(x, y)))

def tx(+a: Laws.Act, +x: Nat, +y: Nat) -> Nat:
  match a:
    case Laws.Up{}:
      x
    case Laws.Down{}:
      x
    case Laws.Left{}:
      warp_left(x)
    case Laws.Right{}:
      warp_right(x)
    case Laws.Grab{}:
      x

def ty(+a: Laws.Act, +x: Nat, +y: Nat) -> Nat:
  match a:
    case Laws.Up{}:
      warp_up(y)
    case Laws.Down{}:
      warp_down(y)
    case Laws.Left{}:
      y
    case Laws.Right{}:
      y
    case Laws.Grab{}:
      y

def chk(+a: Laws.Act, +x: Nat, +y: Nat) -> Bool:
  imp(okpos(x, y) && Bool.not(wall(tx(a, x, y), ty(a, x, y))),
    okpos(tx(a, x, y), ty(a, x, y)))

def chk_row(+a: Laws.Act, +x: Nat, y: Nat) -> Bool:
  match y:
    case 0n:
      chk(a, x, 0n)
    case 1n+q0:
      +q = q0
      chk(a, x, 1n+q) && chk_row(a, x, q)

def chk_all(+a: Laws.Act, x: Nat) -> Bool:
  match x:
    case 0n:
      chk_row(a, 0n, 9n)
    case 1n+p0:
      +p = p0
      chk_row(a, 1n+p, 9n) && chk_all(a, p)

def chk_row_at(+a: Laws.Act, +x: Nat, y: Nat, j: Nat, wr: T(chk_row(a, x, y)),
  wj: T(nat_le(j, y))) -> T(chk(a, x, j)):
  match y:
    case 0n:
      match j:
        case 0n:
          wr
        case 1n+jp:
          Empty.absurd(T(chk(a, x, 1n+jp)), wj)
    case 1n+q0:
      match j:
        case 0n:
          +q = q0
          and_split(chk(a, x, 1n+q), chk_row(a, x, q), wr, T(chk(a, x, 0n)),
            wp => wt => chk_row_at(a, x, q, 0n, wt, Unit{}))
        case 1n+jp0:
          +q = q0
          +jp = jp0
          and_split(chk(a, x, 1n+q), chk_row(a, x, q), wr, T(chk(a, x, 1n+jp)),
            wp => wt =>
              or_case(T(nat_le(1n+jp, q)), {jp == q : Nat},
                le_split(jp, q, wj), T(chk(a, x, 1n+jp)),
                l => chk_row_at(a, x, q, 1n+jp, wt, l),
                e => %sym(Nat, jp, q, e) : T(chk(a, x, 1n+_))
                     wp))

def chk_all_at(+a: Laws.Act, x: Nat, i: Nat, wa: T(chk_all(a, x)),
  wi: T(nat_le(i, x))) -> T(chk_row(a, i, 9n)):
  match x:
    case 0n:
      match i:
        case 0n:
          wa
        case 1n+ip:
          Empty.absurd(T(chk_row(a, 1n+ip, 9n)), wi)
    case 1n+p0:
      match i:
        case 0n:
          +p = p0
          and_split(chk_row(a, 1n+p, 9n), chk_all(a, p), wa,
            T(chk_row(a, 0n, 9n)),
            wp => wt => chk_all_at(a, p, 0n, wt, Unit{}))
        case 1n+ip0:
          +p = p0
          +ip = ip0
          and_split(chk_row(a, 1n+p, 9n), chk_all(a, p), wa,
            T(chk_row(a, 1n+ip, 9n)),
            wp => wt =>
              or_case(T(nat_le(1n+ip, p)), {ip == p : Nat},
                le_split(ip, p, wi), T(chk_row(a, 1n+ip, 9n)),
                l => chk_all_at(a, p, 1n+ip, wt, l),
                e => %sym(Nat, ip, p, e) : T(chk_row(a, 1n+_, 9n))
                     wp))

def cert(+a: Laws.Act, +x: Nat, +y: Nat, ca: T(chk_all(a, 13n)),
  lx: T(nat_le(x, 13n)), ly: T(nat_le(y, 9n))) -> T(chk(a, x, y)):
  chk_row_at(a, x, 9n, y, chk_all_at(a, 13n, x, ca, lx), ly)

# the safe target: from a safe cell, a step lands on a wall or stays safe
def go_ok(+a: Laws.Act, +x: Nat, +y: Nat, +hp: T(okpos(x, y)),
  ca: T(chk_all(a, 13n)), e: {False{} == wall(tx(a, x, y), ty(a, x, y)) : Bool})
  -> T(okpos(tx(a, x, y), ty(a, x, y))):
  and_split(nat_le(x, 13n) && nat_le(y, 9n),
    Bool.not(room(x, y)) && Bool.not(wall(x, y)), hp,
    T(okpos(tx(a, x, y), ty(a, x, y))),
    wb => wnr =>
      and_split(nat_le(x, 13n), nat_le(y, 9n), wb,
        T(okpos(tx(a, x, y), ty(a, x, y))),
        lx => ly =>
          imp_elim(okpos(x, y) && Bool.not(wall(tx(a, x, y), ty(a, x, y))),
            okpos(tx(a, x, y), ty(a, x, y)),
            cert(a, x, y, ca, lx, ly),
            and_intro(okpos(x, y),
              Bool.not(wall(tx(a, x, y), ty(a, x, y))),
              hp,
              %e : T(Bool.not(_))
              Unit{}))))

# grabbing off the flag never wins; on the flag is impossible from safety
def no_flag(+x: Nat, +y: Nat, +hp: T(okpos(x, y)),
  e: {True{} == nat_eq(x, flag_x()) && nat_eq(y, flag_y()) : Bool}) -> Empty:
  and_split(nat_eq(x, 1n), nat_eq(y, 1n),
    %e : T(_)
    Unit{},
    Empty,
    wex => wey =>
      and_split(nat_le(x, 13n) && nat_le(y, 9n),
        Bool.not(room(x, y)) && Bool.not(wall(x, y)), hp,
        Empty,
        wb => wrw =>
          and_split(Bool.not(room(x, y)), Bool.not(wall(x, y)), wrw, Empty,
            wnr => wnw =>
              not_elim(room(x, y), wnr,
                %sym(Nat, x, 1n, eq_sound(x, 1n, wex)) : T(nat_le(_, 3n) && nat_le(y, 2n))
                %sym(Nat, y, 1n, eq_sound(y, 1n, wey)) : T(nat_le(1n, 3n) && nat_le(_, 2n))
                Unit{}))))

# the chosen cell: a step from a safe cell lands somewhere safe (or stays)
def go_pos(+a: Laws.Act, +x: Nat, +y: Nat, hp: T(okpos(x, y)),
  ca: T(chk_all(a, 13n)))
  -> &nx: Nat -> &ny: Nat -> T(okpos(nx, ny))
   & {Laws.Game{nx, ny, False{}}
      == move(tx(a, x, y), ty(a, x, y), Laws.Game{x, y, False{}}) : Laws.Game}:
  +hp2 = hp
  pick_split(Laws.Game,
    gz => &nx: Nat -> &ny: Nat -> T(okpos(nx, ny))
        & {Laws.Game{nx, ny, False{}} == gz : Laws.Game},
    wall(tx(a, x, y), ty(a, x, y)),
    Laws.Game{x, y, False{}},
    Laws.Game{tx(a, x, y), ty(a, x, y), False{}},
    et => (x, (y, (hp2, {==}))),
    ef => (tx(a, x, y), (ty(a, x, y), (go_ok(a, x, y, hp2, ca, ef), {==}))))

def use4(-a: Laws.Act, -x: Nat, -y: Nat,
  w: &nx: Nat -> &ny: Nat -> T(okpos(nx, ny))
   & {Laws.Game{nx, ny, False{}}
      == move(tx(a, x, y), ty(a, x, y), Laws.Game{x, y, False{}}) : Laws.Game},
  -P: Type,
  k: @nx: Nat -> @ny: Nat -> @hq: T(okpos(nx, ny))
   -> @eq: {Laws.Game{nx, ny, False{}}
            == move(tx(a, x, y), ty(a, x, y), Laws.Game{x, y, False{}}) : Laws.Game}
   -> P) -> P:
  (nx, w1) = w
  (ny, w2) = w1
  (hq, eq) = w2
  k(nx, ny, hq, eq)

# The theorem's engine# The theorem's engine# The theorem's engine: from any safe unwon state, no action list wins.
def run_false(t: List<Laws.Act>, x: Nat, y: Nat, hp: T(okpos(x, y)))
  -> {Laws.won(Laws.run(t, Laws.Game{x, y, False{}})) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{Laws.Up{}, as0}:
      +x2 = x
      +y2 = y
      use4(Laws.Up{}, x2, y2, go_pos(Laws.Up{}, x2, y2, hp, Unit{}),
        {Laws.won(Laws.run(as0, move(tx(Laws.Up{}, x2, y2), ty(Laws.Up{}, x2, y2),
          Laws.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Laws.won(Laws.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Laws.Down{}, as0}:
      +x2 = x
      +y2 = y
      use4(Laws.Down{}, x2, y2, go_pos(Laws.Down{}, x2, y2, hp, Unit{}),
        {Laws.won(Laws.run(as0, move(tx(Laws.Down{}, x2, y2), ty(Laws.Down{}, x2, y2),
          Laws.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Laws.won(Laws.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Laws.Left{}, as0}:
      +x2 = x
      +y2 = y
      use4(Laws.Left{}, x2, y2, go_pos(Laws.Left{}, x2, y2, hp, Unit{}),
        {Laws.won(Laws.run(as0, move(tx(Laws.Left{}, x2, y2), ty(Laws.Left{}, x2, y2),
          Laws.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Laws.won(Laws.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Laws.Right{}, as0}:
      +x2 = x
      +y2 = y
      use4(Laws.Right{}, x2, y2, go_pos(Laws.Right{}, x2, y2, hp, Unit{}),
        {Laws.won(Laws.run(as0, move(tx(Laws.Right{}, x2, y2), ty(Laws.Right{}, x2, y2),
          Laws.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Laws.won(Laws.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Laws.Grab{}, as0}:
      +x2 = x
      +y2 = y
      +hp2 = hp
      bool_case(nat_eq(x2, flag_x()) && nat_eq(y2, flag_y()),
        z => {Laws.won(Laws.run(as0, Laws.Game{x2, y2, z})) == False{} : Bool},
        et => Empty.absurd(
          {Laws.won(Laws.run(as0, Laws.Game{x2, y2, True{}})) == False{} : Bool},
          no_flag(x2, y2, hp2, et)),
        ef => run_false(as0, x2, y2, hp2))

# The law, filled: the start cell is safe (checked by computation), and
# run_false carries that safety through any list of actions.
def Laws.winning_is_a_bug(t):
  run_false(t, start_x(), start_y(), Unit{})

def main() -> IO(Unit):
  do IO<Unit>:
    u : Unit <- IO.print(grid(Nat.sub(map_h(), 1n)))
    IO.print(pick(String, Laws.won(Laws.run([Laws.Left{}, Laws.Left{}, Laws.Up{}, Laws.Grab{}], Laws.init())),
      "WON (this line is unreachable)", "still not won"))
