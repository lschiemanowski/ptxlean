#!/usr/bin/env python3
"""Check the pinned integration sources and exact public dependency endpoints.

No dependency update, clone, cache download, or external model invocation.
This source guard and proof audit do not establish semantic fidelity.
"""
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_proofs import FORBIDDEN, code_only
from worker_replay import audit_dependencies

COUNTS = {"PtxTorchLean": 7, "PtxTorchLean.TensorBridge": 15,
          "Ptx.Binary32": 25, "Ptx.Binary32.Examples": 16,
          "Ptx.Binary32.Bounds": 12, "Ptx.Binary32.Error": 10,
          "Ptx.Scalar.Binary32": 22, "Ptx.Scalar.Binary32.Text": 6,
          "Ptx.Scalar.Mixed": 27, "Ptx.Scalar.Mixed.Event": 3, "Ptx.Scalar.Mixed.Path": 6, "Ptx.Scalar.Mixed.Run": 8, "Ptx.Scalar.Affine": 47}
TARGETS = {"PtxTorchLean", "PtxTensorBridge", "PtxBinary32",
           "PtxBinary32Examples", "PtxBinary32Bounds", "PtxBinary32Error",
           "PtxBinary32.Instructions", "PtxBinary32.Mixed", "PtxBinary32.Affine"}

# Explicit public coverage for the serialized two-kernel and exact VJP slice.
COUNTS.update({
    "Ptx.Scalar.Sequential": 17,
    "Ptx.Scalar.Sequential.SuccessfulLaunch": 15,
    "Ptx.Scalar.Sequential.Chain": 7,
    "PtxTorchLean.AffineSquareVJP": 10,
    "Ptx.Binary32.SquareError": 8,
    "PtxTorchLean.AffineSquareKernel": 23,
})
TARGETS.update({"PtxBinary32.SquareError", "PtxBinary32.Sequential", "PtxAffineSquareVJP", "PtxAffineSquareKernel"})

# Separately authored backward execution and its actual generated-VJP observation.
COUNTS.update({
    "Ptx.Binary32.BackwardError": 13,
    "Ptx.GradientView": 18,
    "Ptx.Scalar.BackwardPipeline": 23,
    "Ptx.Scalar.BackwardPipeline.Data": 4,
    "PtxTorchLean.AffineBackward": 21
})
TARGETS.update({"PtxBinary32.BackwardError", "PtxBinary32.BackwardPipeline", "PtxGradientView", "PtxAffineBackward"})

# ReLU neuron, including its explicit differentiability and activation margin.
COUNTS.update({
    "Ptx.Binary32.Relu": 9,
    "Ptx.Scalar.ReluGate": 19,
    "PtxTorchLean.ReluVJP": 11,
    "PtxTorchLean.ReluKernel": 26,
    "PtxTorchLean.ReluKernel.BackwardInputs": 5,
    "PtxTorchLean.ReluKernel.Data": 2,
    "PtxTorchLean.ReluKernel.Evaluation": 1,
    "PtxTorchLean.ReluKernel.Inputs": 2,
    "PtxTorchLean.ReluKernel.Stage": 1,
})
TARGETS.update({"PtxBinary32.Relu", "PtxBinary32.ReluGate", "PtxReluVJP", "PtxReluKernel", "PtxReluAccuracy"})

# Ordered binary32 dot product with universal termination and numerical bounds.
COUNTS["Ptx.Binary32.DotError"] = 10
COUNTS["Ptx.Scalar.Dot"] = 26
COUNTS["Ptx.Scalar.Dot.Examples"] = 9
COUNTS["Ptx.Scalar.Mixed"] += 1
COUNTS["Ptx.Scalar.Mixed.Total"] = 8
TARGETS.update({"PtxBinary32.Total", "PtxBinary32.Dot", "PtxBinary32.DotError", "PtxBinary32.DotExamples"})


# Vector-input ReLU neuron, including all new public definitions and proof endpoints.
COUNTS.update({'PtxTorchLean.VectorVJP': 13, 'PtxTorchLean.VectorKernel': 49, 'PtxTorchLean.VectorKernel.Gradient': 6, 'PtxTorchLean.VectorKernel.Stage': 3, 'PtxTorchLean.VectorKernel.Evaluation': 3, 'PtxTorchLean.VectorKernel.Inputs': 12, 'PtxTorchLean.VectorKernel.BackwardInputs': 7})
TARGETS.update({'PtxVectorKernel', 'PtxVectorVJP', 'PtxVectorAccuracy'})

# Dense-layer foundations; no parallel-kernel correspondence claim.
COUNTS.update({'PtxTorchLean.TensorContext': 3, 'PtxTorchLean.DenseVJP': 22, 'Ptx.Binary32.Reduction': 19, 'Ptx.Binary32.Reduction.Tree': 3, 'Ptx.Binary32.Reduction.RowInput': 3, 'Ptx.Scalar.Parallel': 42})
TARGETS.update({'PtxDenseVJP', 'PtxTensorContext', 'PtxBinary32.Reduction', 'PtxBinary32.ParallelBarrier', 'PtxBinary32.ReductionRelu', 'PtxBinary32.Parallel'})

# Repeated-barrier histories and a completed admitted computed-publication witness.
COUNTS.update({'Ptx.Scalar.Parallel.History': 13, 'Ptx.Scalar.Parallel.Memory': 21, 'Ptx.Scalar.Parallel.Reference': 8, 'Ptx.Scalar.Parallel.Publication': 21, 'Ptx.Scalar.Parallel.Memory.Prior': 4})
TARGETS.update({'PtxBinary32.ParallelReference', 'PtxBinary32.ParallelPublication', 'PtxBinary32.ParallelMemory', 'PtxBinary32.ParallelHistory'})

# Concrete dense forward program and its product-publication proof.
COUNTS.update({'Ptx.Scalar.Parallel.Dense': 61, 'Ptx.Scalar.Parallel.Dense.Shape': 10, 'Ptx.Scalar.Parallel.Segment': 3, 'Ptx.Scalar.Parallel.Dense.Checks': 4})
COUNTS["Ptx.Scalar.Parallel"] += 10
TARGETS.update({'PtxBinary32.DenseLayout', 'PtxBinary32.DenseProducts', 'PtxBinary32.ParallelSegment', 'PtxBinary32.DenseProductPhase', 'PtxBinary32.DenseArithmetic', 'PtxBinary32.DenseAddress', 'PtxBinary32.DenseProgram', 'PtxBinary32.DenseSegments', 'PtxBinary32.DenseChecks'})

# Complete selected dense forward candidate; admission remains separate.
COUNTS["Ptx.Scalar.Parallel.Dense"] += 35
TARGETS.update({'PtxBinary32.DenseOutput', 'PtxBinary32.DenseRoundPhase', 'PtxBinary32.DenseForward', 'PtxBinary32.DenseRounds'})


# Concrete-read execution evidence and checked chronological load sources.
COUNTS["Ptx.Scalar.Parallel"] = COUNTS.get("Ptx.Scalar.Parallel", 0) + 5
COUNTS["Ptx.Scalar.Parallel.ConcreteRuns"] = COUNTS.get("Ptx.Scalar.Parallel.ConcreteRuns", 0) + 1
COUNTS["Ptx.Scalar.Parallel.Replay"] = COUNTS.get("Ptx.Scalar.Parallel.Replay", 0) + 25
COUNTS["Ptx.Scalar.Parallel.Dense"] = COUNTS.get("Ptx.Scalar.Parallel.Dense", 0) + 2
COUNTS["Ptx.Scalar.Parallel.ConcreteSegment"] = COUNTS.get("Ptx.Scalar.Parallel.ConcreteSegment", 0) + 4
TARGETS.update({'PtxBinary32.DenseReplay', 'PtxBinary32.ParallelReplay', 'PtxBinary32.ParallelReplaySources', 'PtxBinary32.ParallelConcrete'})

# Sources and barrier order discharge the existing memory constraints.
COUNTS["Ptx.Scalar.Parallel.Memory.Chronology"] = COUNTS.get("Ptx.Scalar.Parallel.Memory.Chronology", 0) + 24
COUNTS["Ptx.Scalar.Parallel.Dense"] = COUNTS.get("Ptx.Scalar.Parallel.Dense", 0) + 1
TARGETS.update({'PtxBinary32.ParallelChronology', 'PtxBinary32.ParallelSources', 'PtxBinary32.DenseAdmission', 'PtxBinary32.ParallelAdmission'})

# Selected admitted forward outputs compared to the actual TorchLean tensor graph.
COUNTS["Ptx.Binary32.Reduction"] += 5
COUNTS.update({"PtxTorchLean.DenseForward": 3, "PtxTorchLean.DenseForward.Encoding": 3})
TARGETS.update({"PtxBinary32.ReductionPadding", "PtxDenseForward"})

# Arbitrary candidate control order and derived barrier timing; address ownership stays separate.
COUNTS["Ptx.Scalar.Parallel.Control"] = 20
COUNTS["Ptx.Scalar.Parallel.Memory"] += 1
COUNTS["Ptx.Scalar.Parallel.Dense"] += 6
TARGETS.update({"PtxBinary32.ParallelControl", "PtxBinary32.ParallelCompletion",
                "PtxBinary32.ParallelVisibility", "PtxBinary32.DenseControl"})

# Actual emitted addresses and single program writers, independent of candidate values.
COUNTS['Ptx.Scalar.Parallel.AddressControl'] = COUNTS.get('Ptx.Scalar.Parallel.AddressControl', 0) + 31
COUNTS['Ptx.Scalar.Parallel.Dense'] = COUNTS.get('Ptx.Scalar.Parallel.Dense', 0) + 19
TARGETS.update({'PtxBinary32.ParallelAddressControl', 'PtxBinary32.ParallelStoreControl', 'PtxBinary32.DenseAddressControl', 'PtxBinary32.DenseOwnership'})

# Completed executions recover actual enabled stores and collective completions.
COUNTS['Ptx.Scalar.Parallel.Dense'] += 11
COUNTS['Ptx.Scalar.Parallel.Control'] += 7
TARGETS.update({'PtxBinary32.ParallelCoverage', 'PtxBinary32.DenseCoverage'})

# Universal dense forward correctness and explicit empty-output no-launch.
COUNTS['Ptx.Scalar.Parallel.AddressControl'] = COUNTS.get('Ptx.Scalar.Parallel.AddressControl', 0) + 2
COUNTS['Ptx.Scalar.Parallel.Dense'] = COUNTS.get('Ptx.Scalar.Parallel.Dense', 0) + 53
COUNTS['Ptx.Scalar.Parallel.Replay'] = COUNTS.get('Ptx.Scalar.Parallel.Replay', 0) + 2
COUNTS['PtxTorchLean.DenseForward'] = COUNTS.get('PtxTorchLean.DenseForward', 0) + 3
TARGETS.update({'PtxBinary32.DenseDataRun', 'PtxBinary32.DenseGlobalReads', 'PtxBinary32.DenseReadData', 'PtxBinary32.DenseLaunch', 'PtxBinary32.DenseReadSources', 'PtxBinary32.DenseData', 'PtxBinary32.DenseDataMachine', 'PtxBinary32.DenseStoreData', 'PtxBinary32.DenseUniversal', 'PtxBinary32.ParallelWriteValues', 'PtxBinary32.ParallelLoadControl', 'PtxBinary32.DenseDataStep', 'PtxBinary32.DenseDataFP', 'PtxBinary32.DenseLoadControl', 'PtxBinary32.DenseLoadSites', 'PtxBinary32.DenseDataRules'})

# Bounded parallel dense backward and reusable pointwise launch contracts.
COUNTS['Ptx.Scalar.Parallel.Dense'] = COUNTS.get('Ptx.Scalar.Parallel.Dense', 0) + 5
COUNTS['Ptx.Scalar.Parallel.DenseBackward'] = COUNTS.get('Ptx.Scalar.Parallel.DenseBackward', 0) + 24
COUNTS['Ptx.Scalar.Parallel.DenseBackward.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.DenseBackward.Checks', 0) + 1
COUNTS['Ptx.Scalar.Parallel.DenseBackward.Execution'] = COUNTS.get('Ptx.Scalar.Parallel.DenseBackward.Execution', 0) + 3
COUNTS['Ptx.Scalar.Parallel.DenseBackward.Shape'] = COUNTS.get('Ptx.Scalar.Parallel.DenseBackward.Shape', 0) + 5
COUNTS['Ptx.Scalar.Parallel.Pointwise'] = COUNTS.get('Ptx.Scalar.Parallel.Pointwise', 0) + 57
COUNTS['Ptx.Scalar.Parallel.Pointwise.Layout'] = COUNTS.get('Ptx.Scalar.Parallel.Pointwise.Layout', 0) + 1
COUNTS['PtxTorchLean.DenseBackward'] = COUNTS.get('PtxTorchLean.DenseBackward', 0) + 16
COUNTS['PtxTorchLean.DenseBackward.Encoding'] = COUNTS.get('PtxTorchLean.DenseBackward.Encoding', 0) + 8
TARGETS.update({'PtxBinary32.PointwiseProgram', 'PtxBinary32.PointwiseMachine', 'PtxBinary32.DenseBackwardLayout', 'PtxBinary32.PointwiseControl', 'PtxBinary32.DenseLaunchContract', 'PtxBinary32.PointwiseData', 'PtxBinary32.DenseBackwardChecks', 'PtxBinary32.DenseBackwardStorage', 'PtxBinary32.PointwiseExists', 'PtxBinary32.PointwiseLaunch', 'PtxBinary32.PointwiseReads', 'PtxBinary32.PointwiseUniversal', 'PtxDenseBackward'})

# Grid foundations, admitted pointwise launches and universal completed dense forward.
COUNTS['Ptx.Scalar.Parallel.Dense'] = COUNTS.get('Ptx.Scalar.Parallel.Dense', 0) + 1
COUNTS['Ptx.Scalar.Parallel.Grid'] = COUNTS.get('Ptx.Scalar.Parallel.Grid', 0) + 77
COUNTS['Ptx.Scalar.Parallel.Grid.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Checks', 0) + 1
COUNTS['Ptx.Scalar.Parallel.Grid.Config'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Config', 0) + 1
COUNTS['Ptx.Scalar.Parallel.Grid.Control'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Control', 0) + 19
COUNTS['Ptx.Scalar.Parallel.Grid.Memory'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Memory', 0) + 21
COUNTS['Ptx.Scalar.Parallel.Grid.Reference'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Reference', 0) + 4
COUNTS['Ptx.Scalar.Parallel.GridDense'] = COUNTS.get('Ptx.Scalar.Parallel.GridDense', 0) + 44
COUNTS['Ptx.Scalar.Parallel.GridDense.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.GridDense.Checks', 0) + 2
COUNTS['Ptx.Scalar.Parallel.GridDense.LocalData'] = COUNTS.get('Ptx.Scalar.Parallel.GridDense.LocalData', 0) + 5
COUNTS['Ptx.Scalar.Parallel.GridPointwise'] = COUNTS.get('Ptx.Scalar.Parallel.GridPointwise', 0) + 17
COUNTS['PtxTorchLean.GridDenseForward'] = COUNTS.get('PtxTorchLean.GridDenseForward', 0) + 1
TARGETS.update({'PtxBinary32.GridControl', 'PtxBinary32.GridBarrierOrder', 'PtxBinary32.GridCoverage', 'PtxBinary32.GridDenseProgram', 'PtxBinary32.GridGraphOrigins', 'PtxBinary32.GridExecution', 'PtxBinary32.GridMemory', 'PtxBinary32.GridDenseOwnership', 'PtxBinary32.GridPointwise', 'PtxBinary32.GridCompletion', 'PtxBinary32.GridDenseChecks', 'PtxBinary32.GridDenseDataMachine', 'PtxBinary32.GridDenseGlobalReads', 'PtxBinary32.GridPointwiseLaunch', 'PtxBinary32.GridDenseCoverage', 'PtxBinary32.GridUnflatten', 'PtxBinary32.GridDenseReadSources', 'PtxBinary32.GridFlatten', 'PtxBinary32.GridGraph', 'PtxBinary32.GridHistory', 'PtxBinary32.GridReference', 'PtxBinary32.GridDenseAddress', 'PtxBinary32.GridDenseUniversal', 'PtxGridDenseForward', 'PtxBinary32.GridGraphUnique', 'PtxBinary32.GridDenseDataRun', 'PtxBinary32.GridPointwisePadding', 'PtxBinary32.GridInvariants', 'PtxBinary32.GridAccessControl', 'PtxBinary32.GridDenseReadData', 'PtxBinary32.GridChecks', 'PtxBinary32.GridDenseWriter'})

# Completed bounded grid forward and backward, including padded physical storage.
COUNTS['Ptx.Scalar.Parallel'] = COUNTS.get('Ptx.Scalar.Parallel', 0) + 3
COUNTS['Ptx.Scalar.Parallel.ConcreteSegment'] = COUNTS.get('Ptx.Scalar.Parallel.ConcreteSegment', 0) + 1
COUNTS['Ptx.Scalar.Parallel.Dense.Local'] = COUNTS.get('Ptx.Scalar.Parallel.Dense.Local', 0) + 6
COUNTS['Ptx.Scalar.Parallel.Grid'] = COUNTS.get('Ptx.Scalar.Parallel.Grid', 0) + 3
COUNTS['Ptx.Scalar.Parallel.Grid.ConcreteRuns'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.ConcreteRuns', 0) + 1
COUNTS['Ptx.Scalar.Parallel.Grid.Memory.Chronology'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Memory.Chronology', 0) + 27
COUNTS['Ptx.Scalar.Parallel.Grid.Reference'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Reference', 0) + 1
COUNTS['Ptx.Scalar.Parallel.Grid.Replay'] = COUNTS.get('Ptx.Scalar.Parallel.Grid.Replay', 0) + 20
COUNTS['Ptx.Scalar.Parallel.GridDense'] = COUNTS.get('Ptx.Scalar.Parallel.GridDense', 0) + 5
COUNTS['Ptx.Scalar.Parallel.GridDense.Local'] = COUNTS.get('Ptx.Scalar.Parallel.GridDense.Local', 0) + 8
COUNTS['Ptx.Scalar.Parallel.GridDenseBackward'] = COUNTS.get('Ptx.Scalar.Parallel.GridDenseBackward', 0) + 23
COUNTS['Ptx.Scalar.Parallel.GridDenseBackward.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.GridDenseBackward.Checks', 0) + 2
COUNTS['Ptx.Scalar.Parallel.GridDenseBackward.Execution'] = COUNTS.get('Ptx.Scalar.Parallel.GridDenseBackward.Execution', 0) + 3
COUNTS['Ptx.Scalar.Parallel.GridPointwise'] = COUNTS.get('Ptx.Scalar.Parallel.GridPointwise', 0) + 4
COUNTS['PtxTorchLean.GridDenseBackward'] = COUNTS.get('PtxTorchLean.GridDenseBackward', 0) + 8
COUNTS['PtxTorchLean.GridDenseForward'] = COUNTS.get('PtxTorchLean.GridDenseForward', 0) + 1
TARGETS.update({'PtxBinary32.GridReplay', 'PtxBinary32.GridDenseLocalControl', 'PtxBinary32.GridAdmission', 'PtxBinary32.GridSources', 'PtxBinary32.GridDenseExists', 'PtxBinary32.ParallelSegmentSweep', 'PtxBinary32.GridChronology', 'PtxBinary32.GridDenseLocalExists', 'PtxBinary32.GridDenseBackwardLayout', 'PtxBinary32.GridDenseBackwardStorage', 'PtxBinary32.GridPointwiseLogical', 'PtxBinary32.GridDenseBackwardChecks', 'PtxBinary32.GridDenseLaunch', 'PtxBinary32.DenseLocalSegments', 'PtxGridDenseBackward', 'PtxBinary32.GridConcrete'})

def git(directory, *args):
    return subprocess.check_output(["git", "-C", str(directory), *args], text=True).strip()


def dependencies():
    manifest = json.loads((HERE / "lake-manifest.json").read_text())
    checked = 0
    for package in manifest["packages"]:
        if package["type"] == "path":
            if package["name"] != "ptxlean" or (HERE / package["dir"]).resolve() != ROOT:
                raise ValueError(f"Unexpected local dependency: {package['name']}")
            continue
        if package["type"] != "git":
            raise ValueError(f"Unsupported dependency kind: {package['type']}")
        name = package["name"].removeprefix("«").removesuffix("»")
        directory = HERE / manifest["packagesDir"] / name
        if not (directory / ".git").exists():
            raise ValueError(f"Missing pinned dependency {name}; provision it before checking")
        if git(directory, "rev-parse", "HEAD") != package["rev"]:
            raise ValueError(f"Dependency HEAD differs from manifest: {name}")
        if git(directory, "status", "--porcelain", "--untracked-files=no"):
            raise ValueError(f"Tracked dependency files modified: {name}")
        checked += 1
    return checked


def sources():
    paths = []
    for directory, subdirs, files in os.walk(HERE):
        subdirs[:] = [d for d in subdirs if d not in {".lake", ".git", "__pycache__"}]
        paths.extend(Path(directory) / f for f in files if f.endswith(".lean"))
    return sorted(paths)


def snapshot():
    paths = [*sources(), ROOT / "Ptx.lean", *sorted((ROOT / "Ptx").rglob("*.lean")),
             HERE / "check.py", HERE / "check.sh",
             ROOT / "scripts/check_proofs.py", ROOT / "scripts/worker_replay.py",
             ROOT / "scripts/worker_run.py"]
    for directory in (HERE, ROOT):
        paths += [directory / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    if len(sys.argv) != 1:
        raise ValueError("Usage: integration/torchlean/check.sh (no arguments)")
    config = tomllib.loads((HERE / "lakefile.toml").read_text())
    if set(config["defaultTargets"]) != TARGETS:
        raise ValueError("Default integration targets changed; update the explicit audit coverage")
    if (HERE / "lean-toolchain").read_bytes() != (ROOT / "lean-toolchain").read_bytes():
        raise ValueError("Integration and root toolchain pins differ")
    count = dependencies()
    paths = sources()
    for path in paths:
        match = FORBIDDEN.search(code_only(path.read_text()))
        if match:
            raise ValueError(f"{path.relative_to(HERE)}: forbidden proof token {match.group()}")
    driver = HERE / "PtxIntegrationAudit.lean"
    names = re.findall(r"^#print axioms (\S+)\s*$", code_only(driver.read_text()), re.MULTILINE)
    if len(set(names)) != len(names) or Counter(n.rsplit('.', 1)[0] for n in names) != Counter(COUNTS):
        raise ValueError("Missing, duplicate, or unexpected audit endpoint count")
    before = snapshot()
    print(f"Pinned dependencies: {count}; integration Lean source guard: {len(paths)} files.", flush=True)
    try:
        pin = (HERE / "lean-toolchain").read_text().strip()
        prefix = "leanprover/lean4:v"
        if not pin.startswith(prefix):
            raise ValueError(f"Unsupported toolchain pin: {pin}")
        version = subprocess.check_output(
            ["lake", "--no-cache", "env", "lean", "--version"], cwd=HERE, text=True).strip()
        if not version.startswith(f"Lean (version {pin.removeprefix(prefix)},"):
            raise ValueError(f"Actual Lean differs from pin {pin}: {version}")
        print(version, flush=True)
        subprocess.run(["lake", "--no-cache", "build"], cwd=HERE, check=True)
        # Fresh evaluation is required even when the compiled module was cached.
        subprocess.run(["lake", "--no-cache", "env", "lean", "PtxBinary32/DenseChecks.lean"],
                       cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PtxBinary32/DenseBackwardChecks.lean"],
                       cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", 'PtxBinary32/GridChecks.lean'],
                       cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", 'PtxBinary32/GridDenseChecks.lean'],
                       cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PtxBinary32/GridDenseBackwardChecks.lean"],
                       cwd=HERE, check=True)
        audit = subprocess.run(["lake", "--no-cache", "env", "lean", driver.name],
                               cwd=HERE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(audit.stdout, end="", flush=True)
        audit.check_returncode()
        audit_dependencies(audit.stdout, names)
    finally:
        dependencies()
        if snapshot() != before:
            raise ValueError("Checked sources, pins, configuration, or checker changed during verification")
    print(f"Integration check passed: {len(names)} exact dependency reports, only standard Lean axioms.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"Integration check failed: {error}")
