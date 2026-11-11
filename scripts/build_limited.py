#!/usr/bin/env python3
"""Build local Lean modules in dependency order with bounded concurrency."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time


ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^(?:public\s+)?import\s+(\S+)", re.MULTILINE)


def dependencies(targets):
    graph = {}

    def visit(name):
        if name in graph:
            return
        if not re.fullmatch(r"WolfeSimplex(?:\.[A-Za-z0-9_]+)*", name):
            raise ValueError(f"Expected a local WolfeSimplex module name: {name}")
        source = ROOT / (name.replace(".", "/") + ".lean")
        if not source.is_file():
            raise ValueError(f"Local module not found: {name}")
        imports = {dep for dep in IMPORT.findall(source.read_text(encoding="utf-8"))
                   if dep == "WolfeSimplex" or dep.startswith("WolfeSimplex.")}
        graph[name] = imports
        for dep in sorted(imports):
            visit(dep)

    for target in targets:
        visit(target)
    return graph


def main():
    if os.name == "nt":
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", default=["WolfeSimplex"])
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--log", type=Path,
                        default=ROOT / ".lake/build/checks/limited-build.log")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    try:
        graph = dependencies(args.targets or ["WolfeSimplex"])
    except ValueError as error:
        parser.error(str(error))

    pending = set(graph)
    done = set()
    if args.dry_run:
        while pending:
            ready = sorted(name for name in pending if graph[name] <= done)
            if not ready:
                parser.error("Cycle in local module imports")
            for name in ready:
                print(name)
                pending.remove(name)
                done.add(name)
        print(f"{len(done)} local modules; no Lean jobs started.")
        return 0

    lake = shutil.which("lake")
    if lake is None:
        parser.error("lake not found; install elan and the pinned toolchain first")
    args.log.parent.mkdir(parents=True, exist_ok=True)
    stopped = threading.Event()
    children = set()
    lock = threading.Lock()

    def build(name):
        started = time.monotonic()
        if stopped.is_set():
            return 130, "Cancelled before starting.\n", 0.0
        child = subprocess.Popen([lake, "build", name], cwd=ROOT,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 text=True, encoding="utf-8", errors="replace",
                                 start_new_session=(os.name != "nt"))
        with lock:
            children.add(child)
            if stopped.is_set():
                terminate(child)
        try:
            output, _ = child.communicate()
            return child.returncode, output, time.monotonic() - started
        finally:
            with lock:
                children.discard(child)

    def terminate(child):
        if child.poll() is not None:
            return
        try:
            if os.name == "nt":
                subprocess.run(["taskkill", "/PID", str(child.pid), "/T", "/F"],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                               check=False)
            else:
                os.killpg(child.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass

    def stop():
        stopped.set()
        with lock:
            for child in children:
                terminate(child)

    pool = ThreadPoolExecutor(max_workers=args.jobs)
    active = {}
    result = 0
    try:
        with args.log.open("w", encoding="utf-8") as log:
            while pending or active:
                ready = sorted(name for name in pending if graph[name] <= done)
                for name in ready[:args.jobs - len(active)]:
                    pending.remove(name)
                    active[pool.submit(build, name)] = name
                    print(f"Checking {name} ({len(done)}/{len(graph)} completed)", flush=True)
                if not active:
                    raise ValueError("Cycle in local module imports")
                finished, _ = wait(active, timeout=0.2, return_when=FIRST_COMPLETED)
                for future in finished:
                    name = active.pop(future)
                    code, output, elapsed = future.result()
                    log.write(f"\n--- {name} ---\n{output}")
                    log.flush()
                    if code:
                        print(output, end="", flush=True)
                        print(f"FAILED {name}; diagnostics: {args.log}", flush=True)
                        result = code
                        stop()
                        return result
                    done.add(name)
                    print(f"Passed {name} ({elapsed:.1f}s)", flush=True)
        print(f"All {len(done)} local modules passed. Log: {args.log}", flush=True)
    except KeyboardInterrupt:
        print("\nStopping build jobs.", flush=True)
        stop()
        result = 130
    except BaseException:
        stop()
        raise
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    return result


if __name__ == "__main__":
    raise SystemExit(main())
