# Winning Is A Bug -- the certificate.
#
# The proofs. This file imports the game (as Game) and the claims (as
# Laws) and fills every assert the laws make -- an unfilled assert is an
# error, so `bend cert.bend` is the whole verification. Everything here
# is AI-written scaffolding for one def: Laws.winning_is_a_bug.
#
# The shape of the argument: an invariant ("the player stands on a safe
# cell: on the map, not in the room, not on a wall") holds at the start
# and survives every action. The finite geometry is computed, not
# argued: chk_all enumerates the whole map and evaluates to True, and
# the *_at lemmas index that certificate at open coordinates. A grab off
# the flag never sets `won`, and the flag's cell is in the room.

import Base
import ./main.bend as Game
import ./laws.bend as Laws

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
  f: {False{} == c : Bool} -> P(b)) -> P(Game.pick(A, c, a, b)):
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

def eq_sound(a: Nat, b: Nat, w: T(Game.nat_eq(a, b))) -> {a == b : Nat}:
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

def le_split(a: Nat, b: Nat, w: T(Game.nat_le(a, b)))
  -> Or(T(Game.nat_le(1n+a, b)), {a == b : Nat}):
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
          Empty.absurd(Or(T(Game.nat_le(2n+p, 0n)), {1n+p == 0n : Nat}), w)
        case 1n+q:
          or_case(T(Game.nat_le(1n+p, q)), {p == q : Nat}, le_split(p, q, w),
            Or(T(Game.nat_le(2n+p, 1n+q)), {1n+p == 1n+q : Nat}),
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
# chk_all(a, 11n) enumerates every cell of the map and checks that a
# step in direction `a` from a safe cell lands on a wall or on a safe
# cell. The term evaluates to True, so its truth is Unit by conversion,
# and chk_row_at/chk_all_at index that certificate at any coordinates.

def room(+x: Nat, +y: Nat) -> Bool:
  Game.nat_le(x, 2n) && Game.nat_le(y, 2n)

def okpos(+x: Nat, +y: Nat) -> Bool:
  (Game.nat_le(x, 11n) && Game.nat_le(y, 7n))
    && (Bool.not(room(x, y)) && Bool.not(Game.wall(x, y)))

def tx(+a: Game.Move, +x: Nat, +y: Nat) -> Nat:
  match a:
    case Game.Up{}:
      x
    case Game.Down{}:
      x
    case Game.Left{}:
      Game.warp_left(x)
    case Game.Right{}:
      Game.warp_right(x)
    case Game.Grab{}:
      x

def ty(+a: Game.Move, +x: Nat, +y: Nat) -> Nat:
  match a:
    case Game.Up{}:
      Game.warp_up(y)
    case Game.Down{}:
      Game.warp_down(y)
    case Game.Left{}:
      y
    case Game.Right{}:
      y
    case Game.Grab{}:
      y

def chk(+a: Game.Move, +x: Nat, +y: Nat) -> Bool:
  imp(okpos(x, y) && Bool.not(Game.wall(tx(a, x, y), ty(a, x, y))),
    okpos(tx(a, x, y), ty(a, x, y)))

def chk_row(+a: Game.Move, +x: Nat, y: Nat) -> Bool:
  match y:
    case 0n:
      chk(a, x, 0n)
    case 1n+q0:
      +q = q0
      chk(a, x, 1n+q) && chk_row(a, x, q)

def chk_all(+a: Game.Move, x: Nat) -> Bool:
  match x:
    case 0n:
      chk_row(a, 0n, 7n)
    case 1n+p0:
      +p = p0
      chk_row(a, 1n+p, 7n) && chk_all(a, p)

def chk_row_at(+a: Game.Move, +x: Nat, y: Nat, j: Nat, wr: T(chk_row(a, x, y)),
  wj: T(Game.nat_le(j, y))) -> T(chk(a, x, j)):
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
              or_case(T(Game.nat_le(1n+jp, q)), {jp == q : Nat},
                le_split(jp, q, wj), T(chk(a, x, 1n+jp)),
                l => chk_row_at(a, x, q, 1n+jp, wt, l),
                e => %sym(Nat, jp, q, e) : T(chk(a, x, 1n+_))
                     wp))

def chk_all_at(+a: Game.Move, x: Nat, i: Nat, wa: T(chk_all(a, x)),
  wi: T(Game.nat_le(i, x))) -> T(chk_row(a, i, 7n)):
  match x:
    case 0n:
      match i:
        case 0n:
          wa
        case 1n+ip:
          Empty.absurd(T(chk_row(a, 1n+ip, 7n)), wi)
    case 1n+p0:
      match i:
        case 0n:
          +p = p0
          and_split(chk_row(a, 1n+p, 7n), chk_all(a, p), wa,
            T(chk_row(a, 0n, 7n)),
            wp => wt => chk_all_at(a, p, 0n, wt, Unit{}))
        case 1n+ip0:
          +p = p0
          +ip = ip0
          and_split(chk_row(a, 1n+p, 7n), chk_all(a, p), wa,
            T(chk_row(a, 1n+ip, 7n)),
            wp => wt =>
              or_case(T(Game.nat_le(1n+ip, p)), {ip == p : Nat},
                le_split(ip, p, wi), T(chk_row(a, 1n+ip, 7n)),
                l => chk_all_at(a, p, 1n+ip, wt, l),
                e => %sym(Nat, ip, p, e) : T(chk_row(a, 1n+_, 7n))
                     wp))

def cert(+a: Game.Move, +x: Nat, +y: Nat, ca: T(chk_all(a, 11n)),
  lx: T(Game.nat_le(x, 11n)), ly: T(Game.nat_le(y, 7n))) -> T(chk(a, x, y)):
  chk_row_at(a, x, 7n, y, chk_all_at(a, 11n, x, ca, lx), ly)

# the safe target: from a safe cell, a step lands on a wall or stays safe
def go_ok(+a: Game.Move, +x: Nat, +y: Nat, +hp: T(okpos(x, y)),
  ca: T(chk_all(a, 11n)), e: {False{} == Game.wall(tx(a, x, y), ty(a, x, y)) : Bool})
  -> T(okpos(tx(a, x, y), ty(a, x, y))):
  and_split(Game.nat_le(x, 11n) && Game.nat_le(y, 7n),
    Bool.not(room(x, y)) && Bool.not(Game.wall(x, y)), hp,
    T(okpos(tx(a, x, y), ty(a, x, y))),
    wb => wnr =>
      and_split(Game.nat_le(x, 11n), Game.nat_le(y, 7n), wb,
        T(okpos(tx(a, x, y), ty(a, x, y))),
        lx => ly =>
          imp_elim(okpos(x, y) && Bool.not(Game.wall(tx(a, x, y), ty(a, x, y))),
            okpos(tx(a, x, y), ty(a, x, y)),
            cert(a, x, y, ca, lx, ly),
            and_intro(okpos(x, y),
              Bool.not(Game.wall(tx(a, x, y), ty(a, x, y))),
              hp,
              %e : T(Bool.not(_))
              Unit{}))))

# grabbing off the flag never wins; on the flag is impossible from safety
def no_flag(+x: Nat, +y: Nat, +hp: T(okpos(x, y)),
  e: {True{} == Game.nat_eq(x, Game.flag_x()) && Game.nat_eq(y, Game.flag_y()) : Bool}) -> Empty:
  and_split(Game.nat_eq(x, 1n), Game.nat_eq(y, 1n),
    %e : T(_)
    Unit{},
    Empty,
    wex => wey =>
      and_split(Game.nat_le(x, 11n) && Game.nat_le(y, 7n),
        Bool.not(room(x, y)) && Bool.not(Game.wall(x, y)), hp,
        Empty,
        wb => wrw =>
          and_split(Bool.not(room(x, y)), Bool.not(Game.wall(x, y)), wrw, Empty,
            wnr => wnw =>
              not_elim(room(x, y), wnr,
                %sym(Nat, x, 1n, eq_sound(x, 1n, wex)) : T(Game.nat_le(_, 2n) && Game.nat_le(y, 2n))
                %sym(Nat, y, 1n, eq_sound(y, 1n, wey)) : T(Game.nat_le(1n, 2n) && Game.nat_le(_, 2n))
                Unit{}))))

# the chosen cell: a step from a safe cell lands somewhere safe (or stays)
def go_pos(+a: Game.Move, +x: Nat, +y: Nat, hp: T(okpos(x, y)),
  ca: T(chk_all(a, 11n)))
  -> &nx: Nat -> &ny: Nat -> T(okpos(nx, ny))
   & {Game.Game{nx, ny, False{}}
      == Game.move(tx(a, x, y), ty(a, x, y), Game.Game{x, y, False{}}) : Game.Game}:
  +hp2 = hp
  pick_split(Game.Game,
    gz => &nx: Nat -> &ny: Nat -> T(okpos(nx, ny))
        & {Game.Game{nx, ny, False{}} == gz : Game.Game},
    Game.wall(tx(a, x, y), ty(a, x, y)),
    Game.Game{x, y, False{}},
    Game.Game{tx(a, x, y), ty(a, x, y), False{}},
    et => (x, (y, (hp2, {==}))),
    ef => (tx(a, x, y), (ty(a, x, y), (go_ok(a, x, y, hp2, ca, ef), {==}))))

def use4(-a: Game.Move, -x: Nat, -y: Nat,
  w: &nx: Nat -> &ny: Nat -> T(okpos(nx, ny))
   & {Game.Game{nx, ny, False{}}
      == Game.move(tx(a, x, y), ty(a, x, y), Game.Game{x, y, False{}}) : Game.Game},
  -P: Type,
  k: @nx: Nat -> @ny: Nat -> @hq: T(okpos(nx, ny))
   -> @eq: {Game.Game{nx, ny, False{}}
            == Game.move(tx(a, x, y), ty(a, x, y), Game.Game{x, y, False{}}) : Game.Game}
   -> P) -> P:
  (nx, w1) = w
  (ny, w2) = w1
  (hq, eq) = w2
  k(nx, ny, hq, eq)

# The theorem's engine: from any safe unwon state, no action list wins.
def run_false(t: List<Game.Move>, x: Nat, y: Nat, hp: T(okpos(x, y)))
  -> {Game.is_won(Game.run(t, Game.Game{x, y, False{}})) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{Game.Up{}, as0}:
      +x2 = x
      +y2 = y
      use4(Game.Up{}, x2, y2, go_pos(Game.Up{}, x2, y2, hp, Unit{}),
        {Game.is_won(Game.run(as0, Game.move(tx(Game.Up{}, x2, y2), ty(Game.Up{}, x2, y2),
          Game.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Game.is_won(Game.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Game.Down{}, as0}:
      +x2 = x
      +y2 = y
      use4(Game.Down{}, x2, y2, go_pos(Game.Down{}, x2, y2, hp, Unit{}),
        {Game.is_won(Game.run(as0, Game.move(tx(Game.Down{}, x2, y2), ty(Game.Down{}, x2, y2),
          Game.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Game.is_won(Game.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Game.Left{}, as0}:
      +x2 = x
      +y2 = y
      use4(Game.Left{}, x2, y2, go_pos(Game.Left{}, x2, y2, hp, Unit{}),
        {Game.is_won(Game.run(as0, Game.move(tx(Game.Left{}, x2, y2), ty(Game.Left{}, x2, y2),
          Game.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Game.is_won(Game.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Game.Right{}, as0}:
      +x2 = x
      +y2 = y
      use4(Game.Right{}, x2, y2, go_pos(Game.Right{}, x2, y2, hp, Unit{}),
        {Game.is_won(Game.run(as0, Game.move(tx(Game.Right{}, x2, y2), ty(Game.Right{}, x2, y2),
          Game.Game{x2, y2, False{}}))) == False{} : Bool},
        nx => ny => hq => eq =>
          %eq : {Game.is_won(Game.run(as0, _)) == False{} : Bool}
          run_false(as0, nx, ny, hq))
    case Con{Game.Grab{}, as0}:
      +x2 = x
      +y2 = y
      +hp2 = hp
      bool_case(Game.nat_eq(x2, Game.flag_x()) && Game.nat_eq(y2, Game.flag_y()),
        z => {Game.is_won(Game.run(as0, Game.Game{x2, y2, z})) == False{} : Bool},
        et => Empty.absurd(
          {Game.is_won(Game.run(as0, Game.Game{x2, y2, True{}})) == False{} : Bool},
          no_flag(x2, y2, hp2, et)),
        ef => run_false(as0, x2, y2, hp2))

# The law, filled: the start cell is safe (checked by computation), and
# run_false carries that safety through any list of actions.
def Laws.winning_is_a_bug(moves):
  run_false(moves, Game.start_x(), Game.start_y(), Unit{})
