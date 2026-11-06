// Adapter: the real npm base64-js package behind the fvdep adapter protocol.
import { createInterface } from "node:readline";
import { createRequire } from "node:module";

const b64 = createRequire(import.meta.url)("base64-js");
const hex = (u8) => Buffer.from(u8).toString("hex");

for await (const line of createInterface({ input: process.stdin })) {
  const [op, arg = ""] = line.split("\t");
  let out;
  try {
    if (op === "encode") {
      if (!/^([0-9a-f]{2})*$/.test(arg)) throw new Error("bad hex");
      out = `ok\t${b64.fromByteArray(Buffer.from(arg, "hex"))}`;
    } else if (op === "decode") out = `ok\t${hex(b64.toByteArray(arg))}`;
    else out = "unsupported";
  } catch {
    out = "err";
  }
  process.stdout.write(out + "\n");
}
