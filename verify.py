from fractions import Fraction as F
from math import ceil, factorial, gcd
from itertools import product
from decimal import Decimal, localcontext
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys


def require(value, message):
    if not value:
        raise RuntimeError(message)


def fract(x):
    return x - x.numerator // x.denominator


def rough_core(m, t):
    a = factorial(t)
    while (g := gcd(m, a)) > 1:
        m //= g
    return m


def allocations(total, dimension):
    if dimension == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in allocations(total - first, dimension - 1):
                yield (first,) + rest


def embedding_checks():
    counts = {"parameter_pairs": 0, "vertices": 0, "adjacent_edges": 0}
    for d in range(1, 5):
        for t in range(1, 5):
            a = d * factorial(t)
            q = 4 * a + 1
            cores = sorted({rough_core(m, t) for m in range(1, 81)})
            replacements = {}
            previous = 0
            for c in cores:
                r = c + a * (((1 - c) * pow(a, -1, q)) % q)
                lower = max(c, previous)
                if r <= lower:
                    r += ((lower - r) // (a * q) + 1) * a * q
                require(r % a == c % a and r % q == 1, "CRT residue")
                require(gcd(r, factorial(t)) == 1, "rough replacement")
                replacements[c] = r
                previous = r
            vertices = {F(0)}
            images = {F(0): F(0)}
            for m in range(1, 81):
                c = rough_core(m, t)
                new_m = m // c * replacements[c]
                require(new_m > m and new_m % d == m % d and gcd(new_m, q) == 1, "mesh transport")
                for k in range(1, min(t, m) + 1):
                    x, y = F(k, m), F(k - 1, m)
                    fx, fy = F(k, new_m), F(k - 1, new_m)
                    for z, fz in ((x, fx), (y, fy)):
                        require(0 <= fz <= z, "continuity bound")
                        if z in images:
                            require(images[z] == fz, "sample collision preserved")
                        images[z] = fz
                        vertices.add(z)
                    counts["adjacent_edges"] += 1
            require(len(set(images.values())) == len(vertices), "injectivity")
            counts["vertices"] += len(vertices)
            counts["parameter_pairs"] += 1
    return counts


def inverse_checks():
    counts = {"parameter_pairs": 0, "profiles": 0, "progression_instances": 0}
    for d in range(1, 5):
        for tmax in range(1, 5):
            q = 4 * d * factorial(tmax) + 1
            modulus = d * q
            require(q > 4 * tmax and gcd(q, d * factorial(tmax)) == 1, "auxiliary modulus")
            profiles = []
            for t in range(1, tmax + 1):
                top = F(q - 2 * t + 1, 2 * q)
                n = ceil(F(t) / top)
                fs = [top] * (n - 1) + [F(t) - (n - 1) * top]
                require(2 <= n <= 4 * tmax and all(0 < f <= top < F(1, 2) for f in fs), "fractional profile")
                for residue in range(modulus):
                    if gcd(residue, q) != 1:
                        continue
                    g = gcd(residue, modulus)
                    reduced = modulus // g
                    weights = [modulus * f for f in fs]
                    require(all(w.denominator == 1 and int(w) % g == 0 for w in weights), "lattice compatibility")
                    numerators = [(int(w) // g * pow(residue // g, -1, reduced)) % reduced for w in weights]
                    require(all(0 < c < reduced for c in numerators), "least positive representatives")
                    height = ceil(F(sum(numerators), modulus))
                    require(1 <= height <= n and sum(numerators) % reduced == 0, "height criterion")
                    profiles.append((t, residue, fs, numerators, height))
            height = max(row[-1] for row in profiles)
            require(height <= 4 * tmax, "common dilation bound")
            for t, residue, fs, numerators, local_height in profiles:
                cs = numerators.copy()
                cs[0] += height * modulus - sum(cs)
                target = [F(c, height * modulus) for c in cs]
                require(min(target) > 0 and sum(target) == 1, "positive simplex target")
                mesh0 = residue + max(0, ceil(F(t - residue, modulus))) * modulus
                for m in (mesh0, mesh0 + modulus, mesh0 + 7 * modulus):
                    require([fract(height * m * a) for a in target] == fs, "constant progression profile")
                    counts["progression_instances"] += 1
                ordered = sorted(fs, reverse=True)
                costs = [sum(f * f for f in fs) + sum(1 - 2 * f for f in ordered[:j]) + F((t - j) ** 2, q) for j in range(t + 1)]
                require(all(c - costs[0] == F(j * (j - 1), q) for j, c in enumerate(costs)), "constructed profile exact cost identity")
                require(costs[0] == costs[1] and all(c - costs[0] >= F(2, q) for c in costs[2:]), "normalized exclusion gap")
                require(sum(numerators) > (local_height - 1) * modulus, "lower-height exclusion")
                counts["profiles"] += 1
            counts["parameter_pairs"] += 1
    return counts


def compact_checks():
    targets = [("anchor", [F(31, 36), F(4, 36), F(1, 36)], 4), ("residue_one", [F(7, 12)] + [F(1, 12)] * 5, 16), ("residue_two", [F(1, 6)] * 6, 8)]
    counts = {"full_grid_vectors": 0, "profile_meshes": 0, "dyadic_edges": 0}
    delta = min(F(1, mesh) for _, _, mesh in targets)
    alpha = F(1, 100) / (2 * (cutoff_c2_bound(delta) + 1))
    for label, target, first_mesh in targets:
        expected = [F(4, 9), F(4, 9), F(1, 9)] if label == "anchor" else [F(1, 3)] * 6
        for j in range(100):
            m = 1 + 9 * j if label == "anchor" else (4 + 3 * j if label == "residue_one" else 2 + 3 * j)
            require([fract(4 * m * a) for a in target] == expected, "compact progression")
            counts["profile_meshes"] += 1
        mesh = first_mesh
        floors = [int(mesh * a) for a in target]
        slices = {}
        for total in range(mesh + 1):
            for ns in allocations(total, len(target)):
                j = sum(ns) - sum(floors)
                fitting = sum((F(n) - mesh * a) ** 2 for n, a in zip(ns, target))
                slices[j] = min(slices.get(j, fitting), fitting)
                counts["full_grid_vectors"] += 1
        t = mesh - sum(floors)
        costs = {j: c + F((t - j) ** 2, 9) for j, c in slices.items()}
        require({j for j, c in costs.items() if c == min(costs.values())} == {0, 1}, "all-grid baseline indices")
        perturbed = {j: c + (alpha * F(mesh ** 3, t - j) if t - j else 0) for j, c in costs.items()}
        require({j for j, c in perturbed.items() if c == min(perturbed.values())} == ({1} if label == "anchor" else {0}), "finite reciprocal sample witness")
    for n in range(150):
        m = 2 ** (n + 1)
        target = targets[1 if m % 3 == 1 else 2][1]
        require([fract(4 * m * a) for a in target] == [F(1, 3)] * 6, "dyadic coverage")
        require(F(2, 4 * m) == F(1, 4 * 2 ** n), "dyadic source")
        counts["dyadic_edges"] += 1
    return counts


def scalar_and_simplex_checks():
    counts = {"models": 0, "penalty_cases": 0, "grid_vectors": 0, "tied_cases": 0}
    for dimension in range(1, 4):
        for denominator in range(dimension, dimension + 4):
            for positive in allocations(denominator - dimension, dimension):
                target = [F(n + 1, denominator) for n in positive]
                for mesh in range(1, 7):
                    ys = [mesh * x for x in target]
                    floors = [x.numerator // x.denominator for x in ys]
                    fs = [fract(x) for x in ys]
                    capacity = mesh - sum(floors)
                    ordered = sorted(fs, reverse=True)
                    grid = [ns for total in range(mesh + 1) for ns in allocations(total, dimension)]
                    fitting = {}
                    for ns in grid:
                        d = [F(n, mesh) for n in ns]
                        slack = 1 - sum(d)
                        p = d + [slack]
                        require(sum(p) == 1 and min(p) >= 0 and all((mesh * x).denominator == 1 for x in p), "simplex grid embedding")
                        require((p[-1] == 0) == (sum(ns) == mesh), "residual support face")
                        loss = sum((x - y) ** 2 for x, y in zip(d, target))
                        require(sum((x - y) ** 2 for x, y in zip(p, target + [F(0)])) == loss + slack ** 2, "full simplex squared distance")
                        fitting[tuple(ns)] = loss
                        counts["grid_vectors"] += 1
                    for linear, quadratic in [(0, 0), (1, 0), (0, 1), (F(1, 3), F(1, 9))]:
                        values = {ns: loss + linear * (1 - F(sum(ns), mesh)) + quadratic * (1 - F(sum(ns), mesh)) ** 2 for ns, loss in fitting.items()}
                        best = min(values.values())
                        winners = {ns for ns, value in values.items() if value == best}
                        scalar = [sum(f * f for f in fs) + sum(1 - 2 * f for f in ordered[:j]) + linear * mesh * (capacity - j) + quadratic * (capacity - j) ** 2 for j in range(capacity + 1)]
                        indices = {j for j, value in enumerate(scalar) if value == min(scalar)}
                        require({sum(ns) - sum(floors) for ns in winners} == indices, "all scalar minimizing indices")
                        predicted = set()
                        for ns in grid:
                            j = sum(ns) - sum(floors)
                            if j in indices and all(lo <= n <= ceil(y) for n, lo, y in zip(ns, floors, ys)):
                                increment = sum((n - lo) * (1 - 2 * f) for n, lo, f in zip(ns, floors, fs))
                                if increment == sum(1 - 2 * f for f in ordered[:j]):
                                    predicted.add(tuple(ns))
                        require(winners == predicted, "all vector ties retained")
                        require(mesh ** 2 * best == min(scalar), "normalized scalar optimum")
                        counts["tied_cases"] += len(winners) > 1
                        counts["penalty_cases"] += 1
                    counts["models"] += 1
    return counts


def general_profile_checks():
    counts = {"compatible": 0, "incompatible": 0, "height_realizations": 0}
    for modulus in range(2, 8):
        for dimension in range(2, 5):
            for weights in product(range(1, modulus), repeat=dimension):
                if sum(weights) % modulus:
                    continue
                for residue in range(modulus):
                    common = gcd(residue, modulus)
                    compatible = all(w % common == 0 for w in weights)
                    solutions = [[c for c in range(1, modulus + 1) if (residue * c - w) % modulus == 0] for w in weights]
                    require(compatible == all(solutions), "gcd profile criterion")
                    if not compatible:
                        counts["incompatible"] += 1
                        continue
                    representatives = [min(cs) for cs in solutions]
                    require(all(c <= other for cs, c in zip(solutions, representatives) for other in cs), "least positive coordinate representatives")
                    height = ceil(F(sum(representatives), modulus))
                    require(1 <= height <= dimension and sum(representatives) > (height - 1) * modulus, "minimum dilation height")
                    profile = [F(w, modulus) for w in weights]
                    for h in [height, height + 1, height + 3]:
                        padded = representatives.copy()
                        padded[0] += h * modulus - sum(padded)
                        target = [F(c, h * modulus) for c in padded]
                        require(min(target) > 0 and sum(target) == 1, "general padded simplex")
                        for j in [0, 1, 3]:
                            m = h * (residue + j * modulus)
                            require(m > 0 and [fract(m * x) for x in target] == profile, "general real-profile lattice realization")
                        counts["height_realizations"] += 1
                    counts["compatible"] += 1
    for modulus, residue, reps, h, target in [(9, 1, [4, 4, 1], 1, [F(31, 36), F(4, 36), F(1, 36)]), (3, 1, [1] * 6, 2, [F(7, 12)] + [F(1, 12)] * 5), (3, 2, [2] * 6, 4, [F(1, 6)] * 6)]:
        require(ceil(F(sum(reps), modulus)) == h, "displayed minimum heights")
        padded = reps.copy()
        padded[0] += 4 * modulus - sum(padded)
        require([F(c, 4 * modulus) for c in padded] == target, "displayed target synthesis")
    return counts


def cutoff_c2_bound(delta):
    rate = F(3, 2) / delta
    first = 200 * (rate + 1)
    second = 8000 * (rate ** 2 + 1) + 80000 * rate
    return 3 / delta + 3 * first / delta + 9 / delta ** 2 + 3 * second / delta + 18 * first / delta ** 2 + 54 / delta ** 3


def smooth_step_jet(t):
    one = Decimal(1)
    zero = Decimal(0)
    if t <= 0:
        return zero, zero, zero
    if t >= 1:
        return one, zero, zero
    u = one - t
    z = -one / t + one / u
    if z >= 0:
        e = (-z).exp()
        value = one / (one + e)
        variance = e / (one + e) ** 2
    else:
        e = z.exp()
        value = e / (one + e)
        variance = e / (one + e) ** 2
    first = one / t ** 2 + one / u ** 2
    second = -2 / t ** 3 + 2 / u ** 3
    return value, variance * first, variance * ((one - 2 * value) * first ** 2 + second)


def reciprocal_cutoff_jet(delta, s):
    zero = Decimal(0)
    one = Decimal(1)
    if s <= delta / 3 or s >= 2:
        return zero, zero, zero
    rate = 3 / (2 * delta)
    a, ad, add = smooth_step_jet((s - delta / 3) * rate)
    v, vd, vdd = smooth_step_jet(s - 1)
    b, bd, bdd = one - v, -vd, -vdd
    chi = a * b
    first = rate * ad * b + a * bd
    second = rate ** 2 * add * b + 2 * rate * ad * bd + a * bdd
    return chi / s, first / s - chi / s ** 2, second / s - 2 * first / s ** 2 + 2 * chi / s ** 3


def reciprocal_cutoff_checks():
    counts = {"finite_observation_sets": 0, "strict_comparisons": 0, "decimal_jet_samples": 0, "precision": 80}
    selections = [([], [], []), ([0], [], []), ([], [0], []), ([], [], [0]), ([0], [0], [0]), ([0, 2], [0, 3], [0, 4]), ([4], [7], [8])]
    for aa, bb, cc in selections:
        edges = [(F(0), F(1, 4 * (1 + 9 * j))) for j in aa] + [(F(2, 4 * (4 + 3 * j)), F(1, 4 * (4 + 3 * j))) for j in bb] + [(F(2, 4 * (2 + 3 * j)), F(1, 4 * (2 + 3 * j))) for j in cc]
        positive = {x for edge in edges for x in edge if x > 0}
        if not positive:
            require(not edges, "empty observations use the quadratic reference")
            counts["finite_observation_sets"] += 1
            continue
        delta = min(positive)
        bound = cutoff_c2_bound(delta)
        for eta in [F(1, 100), F(1, 10 ** 6)]:
            alpha = min(eta, F(1, 36)) / (2 * (bound + 1))
            require(alpha > 0 and alpha * bound < min(eta, F(1, 36)), "positive small reciprocal-cutoff scale")
            for x, y in edges:
                hx, hy = (alpha / x if x else F(0)), alpha / y
                require(hx < hy, "same quotient witness strict comparison")
                counts["strict_comparisons"] += 1
        counts["finite_observation_sets"] += 1
    with localcontext() as context:
        context.prec = counts["precision"]
        for denominator in [4, 16, 88, 1000]:
            delta_q = F(1, denominator)
            delta = Decimal(1) / Decimal(denominator)
            bound = Decimal(cutoff_c2_bound(delta_q).numerator) / Decimal(cutoff_c2_bound(delta_q).denominator)
            points = {Decimal(-1), Decimal(0), delta / 6, delta / 3, delta, Decimal(1), Decimal(2), Decimal(3)}
            points.update(delta / 3 + 2 * delta * Decimal(i) / 600 for i in range(301))
            points.update(Decimal(1) + Decimal(i) / 300 for i in range(301))
            for s in points:
                jet = reciprocal_cutoff_jet(delta, s)
                require(all(abs(x) <= bound for x in jet), "sampled global quotient derivative envelope")
                if s <= delta / 3 or s >= 2:
                    require(jet == (0, 0, 0), "cutoff zero neighborhoods")
                if delta <= s <= 1:
                    expected = (1 / s, -1 / s ** 2, 2 / s ** 3)
                    require(all(abs(x - y) < Decimal('1e-60') * (1 + abs(y)) for x, y in zip(jet, expected)), "reciprocal plateau and derivatives")
                counts["decimal_jet_samples"] += 1
    return counts


def execute(command, cwd, environment, logfile):
    completed = subprocess.run(command, cwd=cwd, env=environment, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logfile.write_text(completed.stdout)
    require(completed.returncode == 0, f"Command failed ({completed.returncode}); see {logfile}")
    return {"command": command, "exit_code": completed.returncode, "log": str(logfile)}


def lean_checks(repo, output, args):
    require(args.lean_workspace is not None and args.lean_bin is not None, "Lean workspace and executable are required")
    workspace = args.lean_workspace.resolve()
    lean = args.lean_bin.resolve()
    require(workspace.is_dir() and not workspace.is_relative_to(repo), "External mathlib workspace required")
    require(lean.is_file(), "Lean executable missing")
    pinned = "905b95818eb32af7874a58b427f50c1711a5e96c"
    commit = subprocess.run(["git", "-C", str(workspace), "rev-parse", "HEAD"], text=True, capture_output=True, check=True).stdout.strip()
    require(commit == pinned, "Unexpected mathlib revision")
    env = os.environ.copy()
    env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_SYSROOT"] = str(lean.parent.parent)
    out = output / "lean"
    out.mkdir(exist_ok=True)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [out, workspace / ".lake/build/lib/lean", *sorted((workspace / ".lake/packages").glob("*/.lake/build/lib/lean"))]))
    version = subprocess.run([str(lean), "--version"], env=env, text=True, capture_output=True, check=True).stdout.strip()
    require(re.search(r"version 4\.32\.2\b", version) is not None, "Unexpected Lean version")
    source = repo / "Proofs.lean"
    code = source.read_text()
    require(re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|--|/-", code) is None, "Unacceptable proof token or comment")
    names = re.findall(r"^#print axioms (\S+)\s*$", code, re.M)
    require(names and len(names) == len(set(names)), "Missing or duplicate axiom audit names")
    build = execute([str(lean), "-o", str(out / "Proofs.olean"), str(source)], repo, env, out / "build.log")
    inventory = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", (out / "build.log").read_text())
    require([name for name, _ in inventory] == names, "Axiom inventory differs from advertised declarations")
    for name, axioms in inventory:
        used = {x.strip() for x in axioms.split(",") if x.strip()}
        require(used <= {"propext", "Classical.choice", "Quot.sound"}, "Unexpected axiom in " + name)
    replay = execute([str(lean.parent / "leanchecker"), "--fresh", "--verbose", "Proofs"], out, env, out / "replay.log")
    return {"status": "PASS_BUILD_AXIOMS_FRESH_REPLAY", "version": version, "mathlib": commit, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "declarations": len(names), "build": build, "replay": replay}


def wolfram_checks(repo, output):
    executable = shutil.which("wolframscript")
    require(executable is not None, "WolframScript unavailable")
    command = [executable, "-file", str(repo / "verify.wls"), str(output / "wolfram_results.json")]
    execution = execute(command, repo, os.environ.copy(), output / "wolfram.log")
    report = json.loads((output / "wolfram_results.json").read_text())
    require(report["status"] == "PASS_SCOPED_SYMBOLIC_CHECKS" and all(report["checks"].values()), "Wolfram checks failed")
    return {"execution": execution, "report": report}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--wolfram", action="store_true")
    parser.add_argument("--lean-workspace", type=Path)
    parser.add_argument("--lean-bin", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent
    output = args.output.resolve()
    require(not output.is_relative_to(repo), "Output must be outside the repository")
    require(not args.output.is_symlink(), "Output symlinks are not allowed")
    output.mkdir(parents=True, exist_ok=True)
    result = {"status": "PASS_EXACT_FINITE_AND_SAMPLED_CHECKS", "python": platform.python_version(), "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "embedding": embedding_checks(), "inverse": inverse_checks(), "compact": compact_checks(), "scalar_simplex": scalar_and_simplex_checks(), "general_profiles": general_profile_checks(), "reciprocal_cutoff": reciprocal_cutoff_checks(), "scope": "Exact finite algebra/grid tests plus 80-digit sampled cutoff derivatives. Infinite existence, impossibility and regularity are established separately in Lean. No finite derivative sampling proves a global bound; no novelty or empirical claim is machine-certified."}
    result["lean"] = lean_checks(repo, output, args) if args.all or args.lean else {"status": "NOT_REQUESTED"}
    result["wolfram"] = wolfram_checks(repo, output) if args.all or args.wolfram else {"status": "NOT_REQUESTED"}
    result["status"] = "PASS_REQUESTED_CHECKS"
    path = output / "verification_results.json"
    require(not path.is_symlink() and (not path.exists() or path.stat().st_nlink == 1), "Unsafe output file")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
