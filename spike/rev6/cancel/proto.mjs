// A minimal encoder and decoder for the Restate service protocol frames the A5 test needs.
// Field numbers and message type ids come from service-protocol/dev/restate/service/protocol.proto
// in restatedev/sdk-shared-core v8.3.0; the frame header (type u16, flags u16, length u32, big
// endian) from src/service_protocol/header.rs there.

const varint = (value) => {
  const out = [];
  let rest = BigInt(value);
  while (rest >= 0x80n) {
    out.push(Number((rest & 0x7fn) | 0x80n));
    rest >>= 7n;
  }
  out.push(Number(rest));
  return out;
};
const key = (field, wire) => varint((field << 3) | wire);
const utf8 = (text) => [...new TextEncoder().encode(text)];

/** A varint field. */
export const uint = (field, value) => [...key(field, 0), ...varint(value)];
/** A length-delimited field holding raw bytes, a string or an encoded message. */
export const bytes = (field, content) => {
  const body = typeof content === "string" ? utf8(content) : [...content];
  return [...key(field, 2), ...varint(body.length), ...body];
};

/** Message type ids used here. */
export const TYPE = {
  start: 0x0000, suspension: 0x0001, error: 0x0002, end: 0x0003, awaitingOn: 0x0006,
  input: 0x0400, output: 0x0401, sleep: 0x040c, call: 0x040d, sendSignal: 0x0410,
  sleepDone: 0x800c, callDone: 0x800d, callId: 0x800e, signal: 0xfbff
};
const NAMES = Object.fromEntries(Object.entries(TYPE).map(([name, id]) => [id, name]));

/** One frame: the 8-byte header and the encoded body. */
export const frame = (type, body) => {
  const header = new DataView(new ArrayBuffer(8));
  header.setUint16(0, type);
  header.setUint16(2, 0);
  header.setUint32(4, body.length);
  return Uint8Array.from([...new Uint8Array(header.buffer), ...body]);
};

/** The server's messages the A5 test sends. */
export const messages = {
  start: (knownEntries) => frame(TYPE.start, [
    ...bytes(1, "a5-invocation"), ...bytes(2, "inv_a5"), ...uint(3, knownEntries),
    ...uint(5, 1), ...bytes(6, "")
  ]),
  input: (text) => frame(TYPE.input, bytes(14, bytes(1, text))),
  callId: (completionId, invocationId) => frame(TYPE.callId, [...uint(1, completionId), ...bytes(16, invocationId)]),
  sleepDone: (completionId) => frame(TYPE.sleepDone, [...uint(1, completionId), ...bytes(4, [])]),
  // Signal index 1 is the built-in cancel signal (CANCEL_SIGNAL_ID in the shared core).
  cancel: () => frame(TYPE.signal, [...uint(2, 1), ...bytes(4, [])])
};

const readVarint = (buf, at) => {
  let value = 0n;
  let shift = 0n;
  let pos = at;
  for (;;) {
    const byte = buf[pos++];
    value |= BigInt(byte & 0x7f) << shift;
    if ((byte & 0x80) === 0) return [value, pos];
    shift += 7n;
  }
};

/** Decodes a message body into { field: [values] }; strings stay as Uint8Array. */
export const fields = (body) => {
  const out = {};
  let pos = 0;
  while (pos < body.length) {
    const [tag, next] = readVarint(body, pos);
    const field = Number(tag >> 3n);
    const wire = Number(tag & 7n);
    let value;
    if (wire === 0) [value, pos] = readVarint(body, next);
    else if (wire === 2) {
      const [length, start] = readVarint(body, next);
      value = body.subarray(start, start + Number(length));
      pos = start + Number(length);
    } else throw new Error(`wire type ${wire} not handled`);
    (out[field] ??= []).push(value);
  }
  return out;
};

/** Splits the VM's output bytes into { type, name, body } frames. */
export const splitFrames = (chunks) => {
  const all = Uint8Array.from(chunks.flatMap((c) => [...c]));
  const out = [];
  let pos = 0;
  while (pos + 8 <= all.length) {
    const view = new DataView(all.buffer, pos, 8);
    const type = view.getUint16(0);
    const length = view.getUint32(4);
    out.push({ type, name: NAMES[type] ?? `0x${type.toString(16)}`, body: all.subarray(pos + 8, pos + 8 + length) });
    pos += 8 + length;
  }
  return out;
};

/** Text of a length-delimited field. */
export const text = (value) => (value === undefined ? undefined : new TextDecoder().decode(value));
