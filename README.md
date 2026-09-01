# Winning Is A Bug

A tiny game with one rule: grab the flag and you win. And one feature: it
ships with a **formal proof** that you can't. Not "we tested it a lot" —
a machine-checked theorem, over every input sequence of every length:

```python
assert winning_is_a_bug:
  forall t: List<Act>
  {won(run(t, init())) == False{} : Bool}
```

If you ever see the win screen, the type checker is broken. File a bug.

**Play it:** https://victortaelin.github.io/winning_is_a_bug

## How to work with Bend

This repo is a working example of the intended division of labor:

- [`laws.bend`](laws.bend) is the **human's** file: types and asserts,
  nothing else. An assert states what must be true; it proves nothing.
- [`main.bend`](main.bend) is the **AI's** file. It imports the laws and
  must *fill* every assert — Bend rejects an unfilled assert — so the
  game, the algorithms, and the proofs live here, and all of it may be
  rewritten at will: `bend main.bend` fails the moment a law stops
  holding.

The human maintains the wall; the machine does anything it wants on the
other side of it, except lie.

## How it runs

There is no build script and no generated glue. The browser UI
([`web/main.js`](web/main.js)) imports the game directly:

```js
import Game from "../main.bend";
```

The [bend-lang](https://github.com/HigherOrderCO/bend4) plugin compiles
`.bend` imports on the fly — under bun (dev server and bundler) and under
node (`node --import bend-lang/register`). Every def becomes a function on
`Game`; the UI asks `Game.grid` for the level and sends every keypress
through `Game.run`. The browser never decides anything.

```bash
cd web
bun install         # gets bend-lang
bun run dev         # serves index.html, .bend imports and all
bun run build       # bend-build index.html ../docs
bend ../main.bend --check   # every law must be filled (needs bend on PATH)
```

## The level

The map is a torus: walk off one edge, come back on the opposite one. The
flag sits in a room on the top-left corner, sealed by two walls. Where are
the room's other two walls? On the far edges of the screen — on a torus,
that IS the other side of the room.

```
....#........#
.F..#........#
....#........#
#####........#
..............
..............
.........P....
..............
..............
#####.........
```

## The proof

An invariant — *the player stands on a safe cell: on the map, not in the
room, not on a wall* — holds at the start and survives every action. The
geometric heart (every step from a safe cell lands on a wall or on a safe
cell) is finite, so it is not argued: `chk_all` enumerates the whole map
and the checker evaluates it to `True`. Reflection lemmas index that
certificate at arbitrary coordinates, and a grab off the flag never sets
`won` because the flag's cell is in the room. No axioms, no TODOs, no
`unsafe`: `bend main.bend --check` answers "All 332 definitions check."
