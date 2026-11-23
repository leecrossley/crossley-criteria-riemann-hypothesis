#!/usr/bin/env python3
"""Build the tree module by module and replay each module in the kernel checker.

  LEAN_BIN=/path/to/toolchain/bin MATHLIB=/path/to/built/mathlib4 \\
      python3 tools/build.py [OUT_DIR]

LEAN_BIN holds lean, lake and leanchecker for Lean 4.33.1. MATHLIB is a checkout
of Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474 that has been built, so
that `lake env printenv LEAN_PATH` run inside it lists its objects. OUT_DIR
defaults to .build beside src and must not hold objects from another tree. Set
JOBS=N (default 1) to run up to N module builds in parallel while keeping -j1
inside each lean process.

Every module is compiled at trust level zero. The project modules are compiled
with warnings as errors; a module that fails only for that reason is retried
without it and named in the summary. The run can be resumed, and it stops if
less than 150 MB of disk is free. Exit status 0 means every module compiled and
passed leanchecker.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
import re
import shutil
import subprocess
import sys
import time
from graphlib import TopologicalSorter

HERE = os.path.dirname(os.path.abspath(__file__))
PRJ = os.path.dirname(HERE)
SRC = os.path.join(PRJ, "src")
OUT = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else os.path.join(PRJ, ".build")
LOGS = os.path.join(OUT, "logs")
JOBS = int(os.environ.get("JOBS", "1"))
if JOBS < 1:
    sys.exit("JOBS must be a positive integer")
T = os.environ.get("LEAN_BIN")
M = os.environ.get("MATHLIB")
if not T or not M:
    sys.exit("set LEAN_BIN and MATHLIB; see the header of this file")

env = os.environ.copy()
env["PATH"] = T + os.pathsep + env["PATH"]
LP = subprocess.check_output([os.path.join(T, "lake"), "env", "printenv", "LEAN_PATH"], cwd=M, env=env, text=True).strip()
env["LEAN_PATH"] = os.pathsep.join([OUT, LP])

mods = {}
for dp, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            mods[os.path.relpath(p, SRC)[:-5].replace(os.sep, ".")] = p
deps = {n: [d for d in re.findall(r"^import (\S+)", open(p, encoding="utf-8").read(), re.M) if d in mods] for n, p in mods.items()}
outside = sorted({d for n, p in mods.items() for d in re.findall(r"^import (\S+)", open(p, encoding="utf-8").read(), re.M)
                  if d not in mods and not d.startswith(("Mathlib", "Lean."))})
if outside:
    sys.exit("imports outside this tree and Mathlib: " + ", ".join(outside))

# The analysis modules were written with autoImplicit off; the project core predates that setting.
ANALYSIS = ("Compat.", "PortAudit.", "IndependentLandau.", "Crossley.", "ZetaShared.", "ZetaCount.", "ZetaRegion.",
            "ZetaRamp.", "ZetaPerron.", "ZetaStrip.", "ZetaExplicit.", "ZetaClassical.")
FLAGS_ANALYSIS = ["-DautoImplicit=false", "-DmaxHeartbeats=4000000"]
FLAGS_STRICT = ["-DwarningAsError=true", "-DmaxRecDepth=100000", "-DmaxHeartbeats=6000000"]
FLAGS_RELAXED = ["-DmaxRecDepth=100000", "-DmaxHeartbeats=6000000"]

os.makedirs(LOGS, exist_ok=True)
progress = open(os.path.join(OUT, "progress.log"), "a")


def say(text):
    line = time.strftime("%H:%M:%S", time.gmtime()) + " " + text
    print(line, flush=True)
    progress.write(line + "\n")
    progress.flush()


def build_one(n):
    if shutil.disk_usage(OUT).free < 150 * 2 ** 20:
        return "disk", False
    obj = os.path.join(OUT, *n.split(".")) + ".olean"
    mark = os.path.join(LOGS, n + ".ok")
    if os.path.exists(obj) and os.path.exists(mark):
        return "cached", False
    os.makedirs(os.path.dirname(obj), exist_ok=True)
    attempts = [FLAGS_ANALYSIS] if n.startswith(ANALYSIS) else [FLAGS_STRICT, FLAGS_RELAXED]
    rc, was_relaxed = 1, False
    for i, flags in enumerate(attempts):
        with open(os.path.join(LOGS, n + ".compile.log"), "w") as w:
            rc = subprocess.run([os.path.join(T, "lean"), "--trust=0", "--tstack=400000", "-j1", *flags, "--root=" + SRC, "-o", obj, mods[n]],
                                cwd=SRC, env=env, stdout=w, stderr=subprocess.STDOUT).returncode
        if rc == 0:
            was_relaxed = (i == 1)
            break
    if rc != 0:
        return "compile_failed", False
    with open(os.path.join(LOGS, n + ".checker.log"), "w") as w:
        rc = subprocess.run([os.path.join(T, "leanchecker"), "-v", n], cwd=M, env=env, stdout=w, stderr=subprocess.STDOUT).returncode
    if rc != 0:
        return "checker_failed", was_relaxed
    open(mark, "w").close()
    return "ok", was_relaxed


failed, relaxed, done = [], [], 0


def record(n, kind, was_relaxed):
    global done
    if kind == "disk":
        say("stopped: under 150 MB of disk free")
        sys.exit(3)
    if was_relaxed:
        relaxed.append(n)
    if kind == "compile_failed":
        failed.append(n)
        say(f"FAILED to compile {n}")
    elif kind == "checker_failed":
        failed.append(n)
        say(f"FAILED in leanchecker: {n}")
    else:
        done += 1
        if kind == "ok" and done % 10 == 0:
            say(f"{done} of {len(mods)} compiled and replayed")


say(f"start, {len(mods)} modules" + (f" (JOBS={JOBS})" if JOBS > 1 else ""))
if JOBS == 1:
    for n in TopologicalSorter(deps).static_order():
        if any(d in failed for d in deps[n]):
            failed.append(n)
            continue
        record(n, *build_one(n))
else:
    ts = TopologicalSorter(deps)
    ts.prepare()
    ready_queue, running = [], {}
    with ThreadPoolExecutor(max_workers=JOBS) as pool:
        while ts.is_active():
            for n in sorted(ts.get_ready()):
                if any(d in failed for d in deps[n]):
                    failed.append(n)
                    ts.done(n)
                else:
                    ready_queue.append(n)
            while ready_queue and len(running) < JOBS:
                n = ready_queue.pop(0)
                running[pool.submit(build_one, n)] = n
            if not running:
                if ready_queue or ts.is_active():
                    continue
                break
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for fut in finished:
                n = running.pop(fut)
                record(n, *fut.result())
                ts.done(n)
say(f"done: {done} passed, {len(failed)} failed, of {len(mods)}")
if relaxed:
    say("compiled without warnings as errors: " + ", ".join(relaxed))
if failed:
    say("failed or blocked: " + ", ".join(failed))
sys.exit(1 if failed else 0)
