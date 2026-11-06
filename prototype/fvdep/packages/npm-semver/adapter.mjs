// Adapter: the real npm semver package behind the fvdep adapter protocol.
// parse   → semver.valid(text)        (normalized version text, or null = err)
// compare → semver.compare(a, b)      (-1 | 0 | 1 → lt | eq | gt; a throw = err)
import { createInterface } from "node:readline";
import { createRequire } from "node:module";

const semver = createRequire(import.meta.url)("semver");
const ord = { "-1": "lt", 0: "eq", 1: "gt" };

for await (const line of createInterface({ input: process.stdin })) {
  const [op, a = "", b = ""] = line.split("\t");
  let out;
  try {
    if (op === "parse") {
      const v = semver.valid(a);
      out = v === null ? "err" : `ok\t${v}`;
    } else if (op === "compare") {
      const r = ord[semver.compare(a, b)];
      out = r === undefined ? "err" : `ok\t${r}`;
    } else out = "unsupported";
  } catch {
    out = "err";
  }
  process.stdout.write(out + "\n");
}
