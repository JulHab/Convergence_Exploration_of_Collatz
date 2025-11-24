#!/usr/bin/env python3
import os
import json
import csv
import ast
from pathlib import Path

# ------------------------------------------------------------
# Helpers
# ------------------------------------------------------------

def parse_global_report(path: Path):
    data = {}
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if not line or "=" not in line:
                continue
            key, val = line.split("=", 1)
            key = key.strip()
            val = val.strip()
            if val in ("True", "False"):
                data[key] = (val == "True")
            else:
                try:
                    data[key] = int(val)
                except ValueError:
                    try:
                        data[key] = ast.literal_eval(val)
                    except Exception:
                        data[key] = val
    return data


def parse_deep_snapshots(path: Path):
    """
    Expects deep_snapshots.txt with header like:
    depth,a,t,delta,has_contract,threshold_est,tension,v2_last,n_mod
    """
    snaps = []
    with open(path, "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            depth = int(row["depth"])
            a = int(row["a"])
            t = int(row["t"])
            b = int(row["b"])
            delta = int(row["delta"])  # not used directly yet
            has_contract_str = row["has_contract"].strip()
            has_contract = has_contract_str.lower() == "true"
            v2_last_raw = row["v2_last"].strip()
            if v2_last_raw in ("", "None", "none", "NA", "na"):
                v2_last = None
            else:
                v2_last = int(float(v2_last_raw))
            n_mod = int(row["n_mod"])

            snaps.append(
                {
                    "depth": depth,
                    "a": a,
                    "t": t,
                    "b": b,
                    "delta": delta,
                    "has_contract": has_contract,
                    "v2_last": v2_last,
                    "n_mod": n_mod,
                }
            )
    return snaps


def load_config(path: Path):
    with open(path, "r") as f:
        return json.load(f)


def z_literal(n: int) -> str:
    return f"{n}%Z"


def bool_to_coq(b: bool) -> str:
    return "true" if b else "false"


# ------------------------------------------------------------
# Main generator
# ------------------------------------------------------------

def build_coq_certificate(run_dir: str, out_path: str = None):
    run_dir = Path(run_dir)
    if out_path is None:
        out_path = Path("src") / "CertificateData.v"
    else:
        out_path = Path(out_path)

    config_path = run_dir / "config.json"
    global_report_path = run_dir / "global_report.txt"
    deep_snapshots_path = run_dir / "deep_snapshots.txt"

    if not config_path.exists():
        raise FileNotFoundError(f"Missing {config_path}")
    if not global_report_path.exists():
        raise FileNotFoundError(f"Missing {global_report_path}")
    if not deep_snapshots_path.exists():
        raise FileNotFoundError(f"Missing {deep_snapshots_path}")

    cfg = load_config(config_path)
    report = parse_global_report(global_report_path)
    snaps = parse_deep_snapshots(deep_snapshots_path)

    any_monster = bool(report.get("any_monster", False))
    deepest_depth = int(report.get("deepest_depth_overall", 0))
    global_max_v2 = int(report.get("global_max_v2", 0))
    BASIN_CUTOFF = int(cfg["BASIN_CUTOFF"])


    # --------------------------------------------------------
    # Write Coq file
    # --------------------------------------------------------
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        f.write("From Coq Require Import ZArith List Bool.\n")
        f.write("From Collatz Require Import CollatzCertificate.\n\n")
        f.write("Open Scope Z_scope.\n\n")
        f.write("Import ListNotations.\n\n")
        f.write(f"Definition BASIN_CUTOFF : Z := {z_literal(BASIN_CUTOFF)}.\n\n")

        # Define the list of StepCertificate
        f.write("Definition collatz_cert_steps : list StepCertificate :=\n")
        if not snaps:
            f.write("  [].\n\n")
        else:
            f.write("  [\n")
            for idx, s in enumerate(snaps):
                depth = s["depth"]
                a = s["a"]
                t = s["t"]
                b = s["b"]
                n_mod = s["n_mod"]
                has_contract = s["has_contract"]
                v2_last = s["v2_last"]

                A = pow(3, a)  # exact; Python bigints are fine

                # v2_last as option Z
                if v2_last is None:
                    v2_coq = "None"
                else:
                    v2_coq = f"(Some {z_literal(v2_last)})"

                # semicolon between elements, NOT comma
                sep = ";" if idx + 1 < len(snaps) else ""
                line = (
                    "    Build_StepCertificate "
                    + z_literal(depth)          # depth_c
                    + " " + z_literal(a)        # a_c
                    + " " + z_literal(t)        # t_c
                    + " " + z_literal(A)        # A_c
                    + " " + z_literal(b)        # b
                    + " " + z_literal(n_mod)    # n_mod_c
                    + " " + v2_coq              # v2_last_c
                    + " " + bool_to_coq(has_contract)  # contract_flag
                    + sep + "\n"
                )
                f.write(line)
            f.write("  ].\n\n")

        # Define the GlobalCertificate
        f.write("Definition collatz_global_certificate : GlobalCertificate :=\n")
        f.write("  Build_GlobalCertificate\n")
        f.write("    collatz_cert_steps\n")
        f.write(f"    {z_literal(deepest_depth)}\n")
        f.write(f"    {bool_to_coq(any_monster)}\n")
        f.write(f"    {z_literal(global_max_v2)}.\n")


    print(f"Wrote Coq certificate to {out_path}")


if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(
        description="Convert Collatz search outputs into a Coq certificate file."
    )
    p.add_argument(
        "run_dir",
        help="Directory containing config.json, global_report.txt, deep_snapshots.txt",
    )
    p.add_argument(
        "--out",
        help="Output Coq file (default: src/CertificateData.v)",
        default=None,
    )
    args = p.parse_args()
    build_coq_certificate(args.run_dir, args.out)
