// build: compiles main.bend to JS, captures the map the Bend program
// prints, and inlines game + map + UI into one self-contained dist/index.html.
//
//   bun build.ts        # writes dist/index.html
//
// Needs `bend` (bend4) on the PATH.

import { $ } from "bun";

const BEND = process.env.BEND ?? "bend";

// 1. Bend -> JS.
await $`mkdir -p .tmp dist`;
await $`${BEND} main.bend --to .tmp/game.js`;

// 2. Run the emitted program: its stdout carries the map grid.
const out  = await $`bun .tmp/game.js`.text();
const grid = out.split("\n").filter((l) => /^[#.FP]+$/.test(l)).join("\n");
if (grid === "") throw new Error("no map grid on the program's stdout");

// 3. The emitted JS, as a library: drop the two CLI driver lines.
const lib = (await Bun.file(".tmp/game.js").text())
  .replace("cli(process.argv.slice(2));", "")
  .replace("io_exit($main$);", "");

// 4. Inline everything into the page.
const ui   = await Bun.file("main.js").text();
const html = (await Bun.file("main.html").text())
  .replace("__GAME_JS__", () => lib)
  .replace("__MAP__", () => JSON.stringify(grid))
  .replace("__UI_JS__", () => ui);

await Bun.write("dist/index.html", html);
console.log(`dist/index.html (${(html.length / 1024).toFixed(1)}kb)`);
