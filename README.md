# Winning Is A Bug

A tiny game with one rule: grab the flag and you win. And one feature: it
ships with a **formal proof** that you can't. Not "we tested it a lot" —
a machine-checked theorem, over every game state and every input sequence:

```python
assert winning_is_a_bug:
  forall t: List<Act>
  {won(run(t, init())) == False{} : Bool}
```

If you ever see the win screen, the type checker is broken. File a bug.

## How it works

The whole game logic — map, movement, wrap-around, grabbing, the `run`
function the theorem quantifies over — is one Bend file:
[`src/main.bend`](src/main.bend). The build compiles it to JS with
[Bend4](https://github.com/HigherOrderCO/bend4) (`bend --to`), captures the
map the program prints, and inlines both plus a small canvas UI
([`src/main.js`](src/main.js)) into one self-contained page. The browser
never decides anything: every keypress goes through the compiled `run`.

```bash
bun build.ts        # needs bend4 on the PATH; writes dist/index.html
open dist/index.html
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

## Status

The game and the wrap are in. The proof, and the pile of skills that will
make you *sure* there must be an exploit, come next.
