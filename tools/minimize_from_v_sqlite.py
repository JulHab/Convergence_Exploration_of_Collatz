#!/usr/bin/env python3
import os, re, json, gzip, sqlite3
from typing import Dict, Iterator, Tuple, Optional

FIELD_RE = re.compile(r"(\w+)\s*:=\s*(.+?)(?:;|\s*\|})")
Z_RE = re.compile(r"\((-?\d+)\)%Z")
SOME_RE = re.compile(r"\(Some\s+\((-?\d+)\)%Z\)")
NONE_RE = re.compile(r"\bNone\b")

def parse_coq_value(v: str):
    v = v.strip()
    m = Z_RE.fullmatch(v)
    if m: return int(m.group(1))
    m = SOME_RE.fullmatch(v)
    if m: return int(m.group(1))
    if NONE_RE.fullmatch(v): return None
    raise ValueError(f"Unparsed Coq value: {v}")

def parse_record(block: str) -> Dict:
    fields = {}
    for k, v in FIELD_RE.findall(block):
        fields[k] = parse_coq_value(v)
    return fields

def iter_records_from_v(path: str) -> Iterator[Dict]:
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        buf = []
        in_rec = False
        for line in f:
            if "{|" in line:
                in_rec = True
                buf = [line]
                if "|}" in line:
                    in_rec = False
                    yield parse_record("".join(buf))
            elif in_rec:
                buf.append(line)
                if "|}" in line:
                    in_rec = False
                    yield parse_record("".join(buf))

def bitlen_nonneg(x: int) -> int:
    return x.bit_length() if x >= 0 else (-x).bit_length()

def hardness_tuple(a: int, b: int, t: int) -> Tuple[int,int,int,int]:
    # larger = harder:
    # - A = 3^a grows with a, so compare a
    # - larger b is harder (compare by bitlen then value)
    # - smaller t is harder => use -t
    return (a, bitlen_nonneg(b), b, -t)

def main(in_dir: str, db_path: str, out_jsonl_gz: str,
         prefix: str = "BucketWitnesses_", suffix: str = ".v",
         commit_every: int = 200_000):

    conn = sqlite3.connect(db_path)
    cur = conn.cursor()
    cur.execute("PRAGMA journal_mode=WAL;")
    cur.execute("PRAGMA synchronous=NORMAL;")

    # Store b as TEXT to avoid 64-bit overflow.
    # Store a (not A) because A=3^a and a is small enough for INTEGER.
    cur.execute("""
        CREATE TABLE IF NOT EXISTS w (
            n_mod INTEGER NOT NULL,
            depth INTEGER NOT NULL,
            a INTEGER NOT NULL,
            t INTEGER NOT NULL,
            b_txt TEXT NOT NULL,
            v2_last INTEGER,
            PRIMARY KEY (n_mod, depth)
        );
    """)
    conn.commit()

    files = [fn for fn in os.listdir(in_dir) if fn.startswith(prefix) and fn.endswith(suffix)]
    files.sort()

    seen = 0
    inserted = 0
    replaced = 0

    for fn in files:
        p = os.path.join(in_dir, fn)
        for rec in iter_records_from_v(p):
            n_mod = rec["n_mod_c"]
            depth = rec["depth_c"]
            a = rec["a_c"]
            t = rec["t_c"]
            b = rec["b_c"]                 # may be huge
            v2_last = rec.get("v2_last_c", None)

            # read existing
            cur.execute("SELECT a, t, b_txt FROM w WHERE n_mod=? AND depth=?", (n_mod, depth))
            row = cur.fetchone()

            if row is None:
                cur.execute(
                    "INSERT INTO w (n_mod, depth, a, t, b_txt, v2_last) VALUES (?,?,?,?,?,?)",
                    (n_mod, depth, a, t, str(b), v2_last),
                )
                inserted += 1
            else:
                a0, t0, b0_txt = row
                b0 = int(b0_txt)

                if hardness_tuple(a, b, t) > hardness_tuple(a0, b0, t0):
                    cur.execute(
                        "UPDATE w SET a=?, t=?, b_txt=?, v2_last=? WHERE n_mod=? AND depth=?",
                        (a, t, str(b), v2_last, n_mod, depth),
                    )
                    replaced += 1

            seen += 1
            if seen % commit_every == 0:
                conn.commit()
                print(f"processed={seen:,} inserted={inserted:,} replaced={replaced:,}")

    conn.commit()
    print(f"FINAL processed={seen:,} inserted={inserted:,} replaced={replaced:,}")

    # Dump minimized set
    with gzip.open(out_jsonl_gz, "wt", encoding="utf-8") as out:
        for n_mod, depth, a, t, b_txt, v2_last in cur.execute(
            "SELECT n_mod, depth, a, t, b_txt, v2_last FROM w ORDER BY depth, n_mod"
        ):
            out.write(json.dumps({
                "n_mod": n_mod,
                "depth": depth,
                "a": a,
                "t": t,
                "b": b_txt,        # keep as string to avoid JSON bigint issues
                "v2_last": v2_last,
            }, separators=(",", ":")) + "\n")

    conn.close()
    print("Wrote minimized:", out_jsonl_gz)

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 4:
        print("usage: minimize_from_v_sqlite.py <in_dir> <out.db> <out.jsonl.gz>")
        raise SystemExit(2)
    main(sys.argv[1], sys.argv[2], sys.argv[3])
