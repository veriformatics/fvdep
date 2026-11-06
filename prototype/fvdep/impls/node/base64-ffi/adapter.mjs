// fvdep adapter over the Node binding (ops encode, decode).
import { createInterface } from "node:readline";
import { encode, decode } from "./index.mjs";

for await (const line of createInterface({ input: process.stdin })) {
  const [op, arg = ""] = line.split("\t");
  let out;
  if (op === "encode") out = /^([0-9a-f]{2})*$/.test(arg) ? `ok\t${encode(Buffer.from(arg, "hex"))}` : "err";
  else if (op === "decode") { const r = decode(arg); out = r === null ? "err" : `ok\t${r.toString("hex")}`; }
  else out = "unsupported";
  process.stdout.write(out + "\n");
}
