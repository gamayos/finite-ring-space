// run-all.js -- aggregate runner for the 1-phase-6 verification suites.
// Runs each suite as a child node process, reports one line per suite,
// exits nonzero if any suite fails. No dependencies.

"use strict";

const { spawnSync } = require("child_process");
const path = require("path");

const SUITES = [
  "verify-233.js",
  "verify-f13.js",
  "verify-sky.js",
  "verify-space.js",
  "verify-hopf.js",
  "verify-render.js",
];

let failed = 0;

for (const suite of SUITES) {
  const file = path.join(__dirname, suite);
  const r = spawnSync(process.execPath, [file], { encoding: "utf8" });
  const out = (r.stdout || "") + (r.stderr || "");
  const ok = r.status === 0;
  if (!ok) failed++;
  const tail = out.trim().split("\n").pop() || "(no output)";
  console.log((ok ? "PASS" : "FAIL") + "  " + suite + "  --  " + tail);
  if (!ok) {
    console.log("---- " + suite + " full output ----");
    console.log(out.trim());
    console.log("----");
  }
}

console.log(
  failed === 0
    ? "ALL SUITES PASS (" + SUITES.length + "/" + SUITES.length + ")"
    : failed + " of " + SUITES.length + " suites FAILED"
);
process.exit(failed === 0 ? 0 : 1);
