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


# Conservative exponential policies and actual encoded base conversion.
COUNTS["Ptx.Binary32.ConservativeULP"] = 16
TARGETS.add("PtxBinary32.ConservativeULP")
COUNTS["Ptx.Binary32.ConservativeULPChecks"] = 6
TARGETS.add("PtxBinary32.ConservativeULPChecks")
COUNTS["Ptx.Binary32.ExpArgument"] = 15
TARGETS.add("PtxBinary32.ExpArgument")
COUNTS["Ptx.Binary32.ExpArgumentChecks"] = 4
TARGETS.add("PtxBinary32.ExpArgumentChecks")


# Bounded exponential numerical provider with exact special cases.
COUNTS["Ptx.Binary32.Exponential"] = 15
TARGETS.add("PtxBinary32.Exponential")
COUNTS["Ptx.Binary32.Exponential.Checks"] = 12
TARGETS.add("PtxBinary32.ExponentialChecks")

COUNTS.update({"Ptx.Scalar.Exponential": 18, "Ptx.Scalar.Exponential.Text": 6})
TARGETS.add("PtxBinary32.ExponentialInstruction")

COUNTS.update({'Ptx.Binary32.ShiftedExp': 6, 'Ptx.Scalar.ShiftedExp': 15, 'Ptx.Scalar.ShiftedExp.Checks': 9})
TARGETS.update(['PtxBinary32.ShiftedExp', 'PtxBinary32.ShiftedExpProgram', 'PtxBinary32.ShiftedExpChecks'])

# Exact finite maximum and fetched parallel reduction.
COUNTS.update({'Ptx.Binary32.Maximum': 8, 'Ptx.Scalar.Parallel.Maximum': 134, 'Ptx.Scalar.Parallel.Maximum.Checks': 9, 'Ptx.Scalar.MaximumSelect': 12, 'Ptx.Binary32.Maximum.Tree': 7})
TARGETS.update(['PtxBinary32.Maximum', 'PtxBinary32.MaximumAddressControl', 'PtxBinary32.MaximumChecks', 'PtxBinary32.MaximumControl', 'PtxBinary32.MaximumCoverage', 'PtxBinary32.MaximumData', 'PtxBinary32.MaximumDataMachine', 'PtxBinary32.MaximumDataRules', 'PtxBinary32.MaximumDataRun', 'PtxBinary32.MaximumDataStep', 'PtxBinary32.MaximumExecution', 'PtxBinary32.MaximumGlobalReads', 'PtxBinary32.MaximumLoadControl', 'PtxBinary32.MaximumLoadSites', 'PtxBinary32.MaximumOwnership', 'PtxBinary32.MaximumProgram', 'PtxBinary32.MaximumReadData', 'PtxBinary32.MaximumReadSources', 'PtxBinary32.MaximumSelect', 'PtxBinary32.MaximumStoreData', 'PtxBinary32.MaximumTree', 'PtxBinary32.MaximumUniversal'])

# Explicit public coverage for the serialized two-kernel and exact VJP slice.
COUNTS.update({'Ptx.Scalar.Reciprocal': 17, 'Ptx.Scalar.Reciprocal.Text': 6})
TARGETS.add('PtxBinary32.ReciprocalInstruction')
COUNTS.update({'Ptx.Binary32.ApproximatePolicyChecks': 7})
TARGETS.add('PtxBinary32.ApproximatePolicyChecks')
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

# Compact row-local scratch: every new public declaration is audited.
COUNTS["Ptx.Scalar.Parallel.Dense.Compact"] = 53
TARGETS.update({'PtxBinary32.CompactDenseDataRules', 'PtxBinary32.CompactDenseControl', 'PtxBinary32.CompactDenseLocalSegments', 'PtxBinary32.CompactDenseAddressControl', 'PtxBinary32.CompactDenseProgram', 'PtxBinary32.CompactDenseDataStep'})

# Conditional softmax arithmetic and the exact TorchLean backward target.
COUNTS.update({'Ptx.Binary32.Approximate': 17, 'Ptx.Numerics.Softmax': 18, 'Ptx.Numerics.Softmax.BackwardStages': 5, 'Ptx.Numerics.Softmax.Checks': 5, 'Ptx.Numerics.Softmax.Stages': 4, 'PtxTorchLean.Softmax': 12})
TARGETS.update({'PtxBinary32.Approximate', 'PtxBinary32.SoftmaxError', 'PtxBinary32.SoftmaxChecks', 'PtxSoftmaxAccuracy'})

# Input-range-derived encoding and rounded reciprocal numerical foundations.
COUNTS.update({'Ptx.Binary32.ApproximateBounds': 6, 'Ptx.Binary32.Reciprocal': 12, 'Ptx.Binary32.Reciprocal.Checks': 9, 'Ptx.Binary32.RoundedReal': 19, 'Ptx.Binary32.RoundedRealChecks': 10})
TARGETS.update({'PtxBinary32.RoundedRealChecks', 'PtxBinary32.ReciprocalChecks', 'PtxBinary32.Reciprocal', 'PtxBinary32.RoundedReal', 'PtxBinary32.ApproximateBounds'})

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
             ROOT / "scripts/worker_run.py",
             ROOT / "formalization/checks/reciprocal-instruction-v2.lean",
             ROOT / "formalization/checks/exponential-instruction-v1.lean"]
    for directory in (HERE, ROOT):
        paths += [directory / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


# Bounded softmax sum and explicit scalar normalization interface.
COUNTS['Ptx.Binary32.Normalize'] = COUNTS.get('Ptx.Binary32.Normalize', 0) + 5
COUNTS['Ptx.Binary32.ShiftedExp'] = COUNTS.get('Ptx.Binary32.ShiftedExp', 0) + 1
COUNTS['Ptx.Binary32.SoftmaxNormalize'] = COUNTS.get('Ptx.Binary32.SoftmaxNormalize', 0) + 4
COUNTS['Ptx.Binary32.SumTree'] = COUNTS.get('Ptx.Binary32.SumTree', 0) + 8
COUNTS['Ptx.Binary32.SumTree.Checks'] = COUNTS.get('Ptx.Binary32.SumTree.Checks', 0) + 5
COUNTS['Ptx.Scalar.Normalize'] = COUNTS.get('Ptx.Scalar.Normalize', 0) + 13
COUNTS['Ptx.Scalar.Normalize.Checks'] = COUNTS.get('Ptx.Scalar.Normalize.Checks', 0) + 5
COUNTS['Ptx.Scalar.Parallel.Sum'] = COUNTS.get('Ptx.Scalar.Parallel.Sum', 0) + 27
COUNTS['Ptx.Scalar.Parallel.Sum.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.Sum.Checks', 0) + 2
COUNTS['Ptx.Scalar.Parallel.SumNormalize'] = COUNTS.get('Ptx.Scalar.Parallel.SumNormalize', 0) + 5
COUNTS['Ptx.Scalar.ShiftedExp'] = COUNTS.get('Ptx.Scalar.ShiftedExp', 0) + 1
TARGETS.update(['PtxBinary32.Normalize', 'PtxBinary32.NormalizeChecks', 'PtxBinary32.NormalizeCorrect', 'PtxBinary32.NormalizeProgram', 'PtxBinary32.ShiftedExpRange', 'PtxBinary32.SoftmaxNormalize', 'PtxBinary32.SumChecks', 'PtxBinary32.SumCorrect', 'PtxBinary32.SumExecution', 'PtxBinary32.SumNormalize', 'PtxBinary32.SumProgram', 'PtxBinary32.SumTree', 'PtxBinary32.SumTreeChecks'])


# Memory-connected reference softmax forward pipeline.
COUNTS['Ptx.Binary32.SoftmaxForward'] = COUNTS.get('Ptx.Binary32.SoftmaxForward', 0) + 8
COUNTS['Ptx.Scalar.Parallel.SoftmaxReductions'] = COUNTS.get('Ptx.Scalar.Parallel.SoftmaxReductions', 0) + 11
COUNTS['Ptx.Scalar.SoftmaxMemory'] = COUNTS.get('Ptx.Scalar.SoftmaxMemory', 0) + 51
COUNTS['Ptx.Scalar.SoftmaxMemory.Checks'] = COUNTS.get('Ptx.Scalar.SoftmaxMemory.Checks', 0) + 5
COUNTS['Ptx.Scalar.SoftmaxPipeline'] = COUNTS.get('Ptx.Scalar.SoftmaxPipeline', 0) + 9
COUNTS['Ptx.Scalar.SoftmaxPipeline.Checks'] = COUNTS.get('Ptx.Scalar.SoftmaxPipeline.Checks', 0) + 2
COUNTS['Ptx.Scalar.SoftmaxStorage'] = COUNTS.get('Ptx.Scalar.SoftmaxStorage', 0) + 7
COUNTS['Ptx.Scalar.SoftmaxSweep'] = COUNTS.get('Ptx.Scalar.SoftmaxSweep', 0) + 6
COUNTS['PtxTorchLean.Softmax'] = COUNTS.get('PtxTorchLean.Softmax', 0) + 3
COUNTS['PtxTorchLean.SoftmaxPipeline'] = COUNTS.get('PtxTorchLean.SoftmaxPipeline', 0) + 7
TARGETS.update(['PtxBinary32.SoftmaxForwardAccuracy', 'PtxBinary32.SoftmaxMemory', 'PtxBinary32.SoftmaxMemoryChecks', 'PtxBinary32.SoftmaxPipeline', 'PtxBinary32.SoftmaxPipelineChecks', 'PtxBinary32.SoftmaxPipelineExists', 'PtxBinary32.SoftmaxReductions', 'PtxBinary32.SoftmaxStorage', 'PtxBinary32.SoftmaxSweep', 'PtxSoftmaxForward', 'PtxSoftmaxPipeline'])


# Parallel elementwise softmax: actual execution, admission and output equivalence.
COUNTS['Ptx.Scalar.ParallelUnary'] = COUNTS.get('Ptx.Scalar.ParallelUnary', 0) + 42
COUNTS['Ptx.Scalar.ParallelUnary.ConcreteRuns'] = COUNTS.get('Ptx.Scalar.ParallelUnary.ConcreteRuns', 0) + 2
COUNTS['Ptx.Scalar.ParallelUnary.Event'] = COUNTS.get('Ptx.Scalar.ParallelUnary.Event', 0) + 4
COUNTS['Ptx.Scalar.ParallelUnary.Memory'] = COUNTS.get('Ptx.Scalar.ParallelUnary.Memory', 0) + 14
COUNTS['Ptx.Scalar.ParallelUnary.Memory.Chronology'] = COUNTS.get('Ptx.Scalar.ParallelUnary.Memory.Chronology', 0) + 23
COUNTS['Ptx.Scalar.ParallelUnary.Runs'] = COUNTS.get('Ptx.Scalar.ParallelUnary.Runs', 0) + 1
COUNTS['Ptx.Scalar.SoftmaxParallel'] = COUNTS.get('Ptx.Scalar.SoftmaxParallel', 0) + 5
COUNTS['Ptx.Scalar.SoftmaxParallel.Checks'] = COUNTS.get('Ptx.Scalar.SoftmaxParallel.Checks', 0) + 2
COUNTS['Ptx.Scalar.UnaryPointwise'] = COUNTS.get('Ptx.Scalar.UnaryPointwise', 0) + 73
COUNTS['Ptx.Scalar.UnaryPointwise.Checks'] = COUNTS.get('Ptx.Scalar.UnaryPointwise.Checks', 0) + 3
COUNTS['PtxTorchLean.SoftmaxParallel'] = COUNTS.get('PtxTorchLean.SoftmaxParallel', 0) + 2
TARGETS.update(['PtxBinary32.ParallelUnary', 'PtxBinary32.ParallelUnaryAdmission', 'PtxBinary32.ParallelUnaryChronology', 'PtxBinary32.ParallelUnaryControl', 'PtxBinary32.ParallelUnaryMemory', 'PtxBinary32.SoftmaxParallel', 'PtxBinary32.SoftmaxParallelChecks', 'PtxBinary32.UnaryPointwiseChecks', 'PtxBinary32.UnaryPointwiseContract', 'PtxBinary32.UnaryPointwiseControl', 'PtxBinary32.UnaryPointwiseCoverage', 'PtxBinary32.UnaryPointwiseData', 'PtxBinary32.UnaryPointwiseExecution', 'PtxBinary32.UnaryPointwiseLaunch', 'PtxBinary32.UnaryPointwiseProgram', 'PtxBinary32.UnaryPointwiseReads', 'PtxBinary32.UnaryPointwiseStored', 'PtxBinary32.UnarySequential', 'PtxSoftmaxParallel'])


# Actual parallel softmax backward and inherited forward-error composition.
COUNTS['Ptx.Binary32.BackwardDot'] = COUNTS.get('Ptx.Binary32.BackwardDot', 0) + 14
COUNTS['Ptx.Binary32.BackwardDot.Checks'] = COUNTS.get('Ptx.Binary32.BackwardDot.Checks', 0) + 4
COUNTS['Ptx.Binary32.SoftmaxBackwardNumeric'] = COUNTS.get('Ptx.Binary32.SoftmaxBackwardNumeric', 0) + 8
COUNTS['Ptx.Scalar.Parallel.Pointwise.DifferenceChecks'] = COUNTS.get('Ptx.Scalar.Parallel.Pointwise.DifferenceChecks', 0) + 1
COUNTS['Ptx.Scalar.Parallel.SoftmaxBackward'] = COUNTS.get('Ptx.Scalar.Parallel.SoftmaxBackward', 0) + 20
COUNTS['Ptx.Scalar.Parallel.SoftmaxBackward.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.SoftmaxBackward.Checks', 0) + 2
COUNTS['Ptx.Scalar.Parallel.SoftmaxBackward.ExecutionChecks'] = COUNTS.get('Ptx.Scalar.Parallel.SoftmaxBackward.ExecutionChecks', 0) + 1
COUNTS['Ptx.Scalar.Parallel.SoftmaxBackwardDot'] = COUNTS.get('Ptx.Scalar.Parallel.SoftmaxBackwardDot', 0) + 15
COUNTS['Ptx.Scalar.Parallel.SoftmaxBackwardDot.Checks'] = COUNTS.get('Ptx.Scalar.Parallel.SoftmaxBackwardDot.Checks', 0) + 1
COUNTS['PtxTorchLean.Softmax'] = COUNTS.get('PtxTorchLean.Softmax', 0) + 3
COUNTS['PtxTorchLean.SoftmaxBackward'] = COUNTS.get('PtxTorchLean.SoftmaxBackward', 0) + 7
TARGETS.update(['PtxBinary32.BackwardDot', 'PtxBinary32.BackwardDotChecks', 'PtxBinary32.BackwardDotFinite', 'PtxBinary32.PointwiseDifferenceChecks', 'PtxBinary32.SoftmaxBackward', 'PtxBinary32.SoftmaxBackwardChecks', 'PtxBinary32.SoftmaxBackwardDot', 'PtxBinary32.SoftmaxBackwardDotChecks', 'PtxBinary32.SoftmaxBackwardDotCorrect', 'PtxBinary32.SoftmaxBackwardExecutionChecks', 'PtxBinary32.SoftmaxBackwardFull', 'PtxBinary32.SoftmaxBackwardLayout', 'PtxBinary32.SoftmaxBackwardNumeric', 'PtxSoftmaxBackward', 'PtxSoftmaxBackwardReference'])


# Restricted hardware export and rejection checks.
COUNTS['Ptx.Hardware.Dense'] = COUNTS.get('Ptx.Hardware.Dense', 0) + 7
COUNTS['Ptx.Hardware.Dense.Checks'] = COUNTS.get('Ptx.Hardware.Dense.Checks', 0) + 5
COUNTS['main'] = COUNTS.get('main', 0) + 1
TARGETS.update(['PtxHardwareDense', 'PtxHardwareDenseChecks', 'HardwareDenseMain'])

# CPU binary64 Poisson reference; no PTX correspondence claim.
COUNTS.update({'PtxTorchLean.Poisson': 28, 'PtxTorchLean.Poisson.CLI': 3, 'PtxTorchLean.Poisson.Checks': 1})
TARGETS.update({'PoissonQuad', 'PoissonQuadCLI', 'PoissonQuadMain', 'PoissonQuadChecks'})

# Poisson ordered computation and exact a posteriori residual certification.
COUNTS.update({'PtxTorchLean.Poisson.Binary64': 6, 'PtxTorchLean.Poisson.Correspondence': 45, 'PtxTorchLean.Poisson.Certificate': 23, 'PtxTorchLean.Poisson.Certificate.Input': 10, 'PtxTorchLean.Poisson.Certificate.Checks': 7})
TARGETS.update({'PoissonResidualMain', 'PoissonQuadCorrespondence', 'PoissonBinary64', 'PoissonResidualChecks', 'PoissonResidualInput', 'PoissonResidualCertificate'})

# Fetched binary64 true_residual slice; parallel admission remains separate.
COUNTS.update({'PtxTorchLean.Poisson.PTX': 62, 'PtxTorchLean.Poisson.PTX.Kernel.Checks': 9, 'PtxTorchLean.Poisson.PTX.Kernel': 25, 'PtxTorchLean.Poisson.PTX.Kernel.Residual': 27, 'PtxTorchLean.Poisson.PTX.FP': 3, 'PtxTorchLean.Poisson.PTX.Operand': 1, 'PtxTorchLean.Poisson.PTX.State': 3, 'PtxTorchLean.Poisson.PTX.Residual': 8, 'PtxTorchLean.Poisson.PTX.Text': 7})
TARGETS.update(['PoissonPTX.Arithmetic', 'PoissonPTX.Bytes', 'PoissonPTX.Checks', 'PoissonPTX.Kernel', 'PoissonPTX.Layout', 'PoissonPTX.Machine', 'PoissonPTX.MemoryBlocks', 'PoissonPTX.Residual', 'PoissonPTX.ResidualKernel', 'PoissonPTX.Tensor', 'PoissonPTX.Text', 'PoissonPTXMain'])

# Byte-source overapproximation and closed parallel residual launch.
COUNTS.update({'PtxTorchLean.Poisson.PTX.Sources': 10, 'PtxTorchLean.Poisson.PTX.Weak': 7, 'PtxTorchLean.Poisson.PTX.Weak.Residual': 4, 'PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel': 16, 'PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Inputs': 1, 'PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena': 9, 'PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Checks': 15})
TARGETS.update(['PoissonPTX.Sources', 'PoissonPTX.Weak', 'PoissonPTX.WeakResidual', 'PoissonPTX.WeakPadding', 'PoissonPTX.ParallelResidual', 'PoissonPTX.ParallelResidualOutput', 'PoissonPTX.ParallelResidualLayout', 'PoissonPTX.ParallelResidualChecks'])

# Fetched binary64 cell contractions and byte-addressed tensor views.
COUNTS["PtxTorchLean.Poisson.PTX"] += 2
COUNTS.update({'PtxTorchLean.Poisson.PTX.Contraction': 54, 'PtxTorchLean.Poisson.PTX.Contraction.Checks': 12, 'PtxTorchLean.Poisson.PTX.Contraction.Coord': 1})
TARGETS.update(['PoissonPTX.Contraction', 'PoissonPTX.ContractionChecks', 'PoissonPTX.ContractionFetched', 'PoissonPTX.ContractionLayout', 'PoissonPTX.ContractionLoads', 'PoissonPTX.ContractionText', 'PoissonContractionsMain'])

COUNTS.update({'PtxTorchLean.Poisson.PTX.SharedStore': 19, 'PtxTorchLean.Poisson.PTX.SharedPlane': 11, 'PtxTorchLean.Poisson.PTX.SharedStore.Checks': 8})
COUNTS["PtxTorchLean.Poisson.PTX.Contraction"] += 1
TARGETS.update(['PoissonPTX.SharedStore', 'PoissonPTX.SharedPlane', 'PoissonPTX.SharedStoreChecks'])

# Fetched binary64 barrier control and necessary byte-source visibility.
COUNTS.update({'PtxTorchLean.Poisson.PTX.Concurrent': 37, 'PtxTorchLean.Poisson.PTX.Concurrent.History': 10, 'PtxTorchLean.Poisson.PTX.Concurrent.Visibility': 8, 'PtxTorchLean.Poisson.PTX.Concurrent.Checks': 26})
TARGETS.update(['PoissonPTX.Concurrent', 'PoissonPTX.ConcurrentHistory', 'PoissonPTX.ConcurrentBarrier', 'PoissonPTX.ConcurrentExec', 'PoissonPTX.ConcurrentOrigins', 'PoissonPTX.ConcurrentOrder', 'PoissonPTX.BarrierSources', 'PoissonPTX.BarrierChecks'])

# Derived producer ordering, non-repetition and shared-plane ownership.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent', 0) + 22
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.ProducerChecks', 0) + 10
TARGETS.update(['PoissonPTX.ConcurrentProducer', 'PoissonPTX.ConcurrentOwnership', 'PoissonPTX.ProducerChecks'])

# Concrete Poisson middle phases and derived store-address coverage.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Address'] = 14
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Padding'] = 6
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle'] = 19
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks'] = 20
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Witness'] = 10
TARGETS.update(['PoissonPTX.ConcurrentAddress', 'PoissonPTX.ConcurrentPadding', 'PoissonPTX.CellMiddle', 'PoissonPTX.CellMiddleChecks', 'PoissonPTX.CellMiddleWitness'])

# Concurrent numerical replay and concrete read-only input storage.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Replay'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Replay', 0) + 17
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Replay.Checks', 0) + 28
TARGETS.update(['PoissonPTX.ConcurrentReplay', 'PoissonPTX.ConcurrentReadOnly', 'PoissonPTX.ConcurrentComputedStore', 'PoissonPTX.CellMiddleInputs', 'PoissonPTX.ConcurrentReplayChecks'])

# Whole middle-phase numerical correspondence and source-constrained witness.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Symbolic'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Symbolic', 0) + 41
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Bits'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Bits', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Number'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.Number', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric', 0) + 49
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Launch', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.WordView', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Geometry', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.Checks', 0) + 9
TARGETS.update(['PoissonPTX.Symbolic', 'PoissonPTX.SymbolicRun', 'PoissonPTX.CellSymbolic', 'PoissonPTX.CellLaunch', 'PoissonPTX.CellWordView', 'PoissonPTX.CellReadGeometry', 'PoissonPTX.CellReadValues', 'PoissonPTX.CellStoreValues', 'PoissonPTX.CellTensor', 'PoissonPTX.CellMiddleCorrespondence', 'PoissonPTX.ZeroSources', 'PoissonPTX.CellMiddleNumericChecks'])

# Final fetched output and composition from actual middle-store bytes.
COUNTS.update({'PtxTorchLean.Poisson.PTX.CellFinal': 43, 'PtxTorchLean.Poisson.PTX.CellFinal.Checks': 13})
TARGETS.update(['PoissonPTX.CellFinal', 'PoissonPTX.CellFinalChecks', 'PoissonPTX.CellFinalKernel', 'PoissonPTX.CellFinalLayout', 'PoissonPTX.CellFinalSnapshot', 'PoissonPTX.CellFinalTensor', 'PoissonPTX.CellFinalText'])

# Concurrent final consumer loads and actual arithmetic-to-store connection.
COUNTS.update({'PtxTorchLean.Poisson.PTX.Concurrent.Extension': 6, 'PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Checks': 13, 'PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer': 32})
TARGETS.update(['PoissonPTX.ConcurrentExtension', 'PoissonPTX.CellConsumerChecks', 'PoissonPTX.CellConsumerOutput', 'PoissonPTX.CellConsumerProgram', 'PoissonPTX.CellConsumerSources', 'PoissonPTX.CellConsumerValues'])

# Derive the last-barrier cut from a single concurrent execution.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Cut'] = 3
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer'] += 3
TARGETS.update({'PoissonPTX.ConcurrentCut', 'PoissonPTX.CellConsumerRun'})

# Byte-source restriction under interleaved disjoint output stores.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Projection'] = 9
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Projection.Checks'] = 17
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients'] = 5
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output'] = 4
TARGETS.update(['PoissonPTX.ConcurrentProjection', 'PoissonPTX.ProjectionChecks', 'PoissonPTX.CellCoefficientProgram', 'PoissonPTX.CellCoefficientReads', 'PoissonPTX.CellOutputSeparation'])

# Combined concurrent output-tail execution and derived arithmetic projection.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Projection'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Projection', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.WithTail'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.WithTail', 0) + 25
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Checks', 0) + 21
TARGETS.update(['PoissonPTX.ProjectionBuild', 'PoissonPTX.ConcurrentTail', 'PoissonPTX.TailFrontProjection', 'PoissonPTX.TailRunProjection', 'PoissonPTX.TailExecute', 'PoissonPTX.CellTailProgram', 'PoissonPTX.CellTailResult', 'PoissonPTX.CellTailChecks', 'PoissonPTX.CellTailWitnessSources'])

# Launch-derived concurrent output-store addresses and actual per-lane bytes.
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address', 0) + 23
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.AddressChecks', 0) + 12
TARGETS.update(['PoissonPTX.CellTailAddress', 'PoissonPTX.CellTailShape', 'PoissonPTX.CellTailFrame', 'PoissonPTX.CellTailStores', 'PoissonPTX.CellTailBounds', 'PoissonPTX.CellTailOwners', 'PoissonPTX.CellTailAddressChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication', 0) + 17
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.PublicationChecks', 0) + 7
TARGETS.update(['PoissonPTX.CellOutputValues', 'PoissonPTX.CellOutputOccurrence', 'PoissonPTX.GlobalPublication', 'PoissonPTX.CellOutputPublication', 'PoissonPTX.CellOutputTensor', 'PoissonPTX.CellPublicationChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.CellPrologue'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellPrologue', 0) + 25
COUNTS['PtxTorchLean.Poisson.PTX.CellPrologue.Context'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellPrologue.Context', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellPrologue.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellPrologue.Checks', 0) + 8
TARGETS.update(['PoissonPTX.CellPrologue', 'PoissonPTX.CellPrologueEntry', 'PoissonPTX.CellPrologueChecks'])

COUNTS['PtxTorchLean.Poisson.PTX'] = COUNTS.get('PtxTorchLean.Poisson.PTX', 0) + 11
COUNTS['PtxTorchLean.Poisson.PTX.Indexed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Indexed', 0) + 20
COUNTS['PtxTorchLean.Poisson.PTX.CellGather'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGather', 0) + 24
COUNTS['PtxTorchLean.Poisson.PTX.CellGather.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGather.Checks', 0) + 9
TARGETS.update(['PoissonPTX.Bytes32', 'PoissonPTX.IndexedMemory', 'PoissonPTX.CellGather', 'PoissonPTX.CellGatherLayout', 'PoissonPTX.CellGatherText', 'PoissonPTX.CellGatherChecks', 'PoissonPTX.CellGatherTensor'])

COUNTS['PtxTorchLean.Poisson'] += 1

COUNTS['PtxTorchLean.Poisson.PTX.IndexSources'] = COUNTS.get('PtxTorchLean.Poisson.PTX.IndexSources', 0) + 10
COUNTS['PtxTorchLean.Poisson.PTX.Indexed.Candidate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Indexed.Candidate', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry', 0) + 48
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Local'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Local', 0) + 13
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Checks', 0) + 26
TARGETS.update(['PoissonPTX.IndexSources', 'PoissonPTX.IndexedCandidate', 'PoissonPTX.CellEntry', 'PoissonPTX.CellEntryInputs', 'PoissonPTX.CellEntryLocal', 'PoissonPTX.CellEntryReplay', 'PoissonPTX.CellEntryResult', 'PoissonPTX.CellEntryBarrier', 'PoissonPTX.CellEntryLaunch', 'PoissonPTX.CellEntryExec', 'PoissonPTX.CellEntryChecks', 'PoissonPTX.CellEntryText'])

COUNTS['PtxTorchLean.Poisson.PTX.CellEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry', 0) + 19
COUNTS['PtxTorchLean.Poisson.PTX.Indexed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Indexed', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Local'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Local', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Local.Avoid'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Local.Avoid', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Producers'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Producers', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.ProducerChecks', 0) + 5
TARGETS.update(['PoissonPTX.CellEntryStores', 'PoissonPTX.CellEntryStorePath', 'PoissonPTX.CellEntryOccurrence', 'PoissonPTX.CellEntryPadding', 'PoissonPTX.CellEntryStoreValue', 'PoissonPTX.CellEntryProducers', 'PoissonPTX.CellEntryProducerChecks', 'PoissonPTX.CellEntryStoreTensor'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry', 0) + 10
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Producers'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Producers', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.VisibilityChecks', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.History'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.History', 0) + 3
TARGETS.update(['PoissonPTX.BarrierValue', 'PoissonPTX.CellEntryHistory', 'PoissonPTX.CellEntryVisibility', 'PoissonPTX.CellGatherPreservation', 'PoissonPTX.CellEntryContinuation', 'PoissonPTX.CellEntryVisibilityChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.SourceCut'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.SourceCut', 0) + 12
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.SourceCheck', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry', 0) + 13
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.RebaseChecks', 0) + 17
TARGETS.update(['PoissonPTX.SourceCut', 'PoissonPTX.SourceCheck', 'PoissonPTX.CellEntryPublication', 'PoissonPTX.CellEntryPublishedTensor', 'PoissonPTX.CellEntryRebase', 'PoissonPTX.CellEntryCorrespondence', 'PoissonPTX.CellEntryRebaseChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Control'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Control', 0) + 54
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.Control.InputLayout'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.Control.InputLayout', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry.JointChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry.JointChecks', 0) + 4
TARGETS.update(['PoissonPTX.CellEntryControl', 'PoissonPTX.CellEntryActive', 'PoissonPTX.CellEntryIndexAddress', 'PoissonPTX.CellEntryInputLayout', 'PoissonPTX.CellEntryIndexInputs', 'PoissonPTX.CellEntrySourceAddress', 'PoissonPTX.CellEntryWordInputs', 'PoissonPTX.CellEntryJointInputs', 'PoissonPTX.CellEntryJointCorrespondence', 'PoissonPTX.CellEntryJointChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Relocate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Relocate', 0) + 47
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.AtOffset'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.AtOffset', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole', 0) + 22
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Relabel'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Relabel', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Clock'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Clock', 0) + 12
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Clock.Progress'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Clock.Progress', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.CellEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellEntry', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.WithTail'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.WithTail', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Checks', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Zero'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Zero', 0) + 22
TARGETS.update(['PoissonPTX.Relocate', 'PoissonPTX.RelocateInverse', 'PoissonPTX.RelocateKernel', 'PoissonPTX.OffsetExecution', 'PoissonPTX.CellWhole', 'PoissonPTX.CellWholeCut', 'PoissonPTX.RelabelHistory', 'PoissonPTX.BarrierClock', 'PoissonPTX.ExecutionClock', 'PoissonPTX.RelabelShift', 'PoissonPTX.CellWholeSources', 'PoissonPTX.CellWholeBounds', 'PoissonPTX.CellWholeCorrespondence', 'PoissonPTX.CellWholeCompose', 'PoissonPTX.CellWholeChecks', 'PoissonPTX.CellWholeZero', 'PoissonPTX.CellWholeText'])

COUNTS['PtxTorchLean.Poisson.PTX.CoefficientRepresentation'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CoefficientRepresentation', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Flow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow', 0) + 28
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Compare'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Compare', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Loop'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Loop', 0) + 8
COUNTS['PtxTorchLean.Poisson.PTX.Indexed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Indexed', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Assembly'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly', 0) + 31
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Checks', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Text'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Text', 0) + 9
TARGETS.update(['PoissonPTX.CellCoefficientRepresentation', 'PoissonPTX.CellOperatorCorrespondence', 'PoissonPTX.ControlFlow', 'PoissonPTX.ControlFlowBlocks', 'PoissonPTX.ControlFlowLoop', 'PoissonPTX.ControlFlowLoopExists', 'PoissonPTX.IndexedBlocks', 'PoissonPTX.AssemblyLookup', 'PoissonPTX.AssemblyLoop', 'PoissonPTX.AssemblyExists', 'PoissonPTX.AssemblyLayout', 'PoissonPTX.AssemblyChecks', 'PoissonPTX.AssemblyText'])

COUNTS['PtxTorchLean.Poisson.PTX.Flow.Window'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Window', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Flow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow', 0) + 12
COUNTS['PtxTorchLean.Poisson.PTX.Assembly'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly', 0) + 56
COUNTS['PtxTorchLean.Poisson.PTX.Indexed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Indexed', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.EntryChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.EntryChecks', 0) + 16
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Text'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Text', 0) + 3
TARGETS.update(['PoissonPTX.ControlFlowWindow', 'PoissonPTX.ControlFlowSequence', 'PoissonPTX.AssemblyWindow', 'PoissonPTX.AssemblyPrologue', 'PoissonPTX.AssemblySetup', 'PoissonPTX.AssemblyMask', 'PoissonPTX.IndexedFrames', 'PoissonPTX.AssemblyOutput', 'PoissonPTX.AssemblyEntry', 'PoissonPTX.AssemblyEntryResult', 'PoissonPTX.ControlFlowWindowExists', 'PoissonPTX.AssemblyWindowExists', 'PoissonPTX.AssemblyInactive', 'PoissonPTX.AssemblyEntryExists', 'PoissonPTX.AssemblyEntryChecks', 'PoissonPTX.AssemblyEntryText'])

COUNTS['PtxTorchLean.Poisson.PTX.Assembly'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Arena', 0) + 27
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Rows'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Rows', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Snapshot'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Snapshot', 0) + 10
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.ArenaChecks', 0) + 11
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Observed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Observed', 0) + 20
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Parallel'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Parallel', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Observed.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Observed.Checks', 0) + 17
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress', 0) + 5
TARGETS.update(['PoissonPTX.AssemblyArena', 'PoissonPTX.AssemblyArenaSafety', 'PoissonPTX.AssemblyArenaValues', 'PoissonPTX.AssemblyRows', 'PoissonPTX.AssemblySnapshotPublication', 'PoissonPTX.AssemblyArenaChecks', 'PoissonPTX.ControlFlowObserved', 'PoissonPTX.ObservedMemoryFrame', 'PoissonPTX.ObservedReplay', 'PoissonPTX.ObservedExists', 'PoissonPTX.ObservedParallel', 'PoissonPTX.ObservedParallelReplay', 'PoissonPTX.ObservedChecks', 'PoissonPTX.AssemblyObservedAddress', 'PoissonPTX.AssemblyObservedStores', 'PoissonPTX.AssemblyParallelStores'])

COUNTS['PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.ObservedAddress', 0) + 24
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Arena', 0) + 19
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.ParallelChecks', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Assembly'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Observed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Observed', 0) + 12
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Parallel'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Parallel', 0) + 6
TARGETS.update(['PoissonPTX.AssemblyBeforeStore', 'PoissonPTX.AssemblyInputSeparation', 'PoissonPTX.AssemblyObservedBounds', 'PoissonPTX.AssemblyObservedIndexBound', 'PoissonPTX.AssemblyObservedOffsets', 'PoissonPTX.AssemblyObservedReadAddress', 'PoissonPTX.AssemblyOffsetRecords', 'PoissonPTX.AssemblyOffsetSources', 'PoissonPTX.AssemblyParallelChecks', 'PoissonPTX.AssemblyParallelCorrespondence', 'PoissonPTX.AssemblyParallelExists', 'PoissonPTX.AssemblyParallelReplay', 'PoissonPTX.AssemblyReadFields', 'PoissonPTX.AssemblyReadFootprints', 'PoissonPTX.AssemblyReadSites', 'PoissonPTX.AssemblyRecordedWitness', 'PoissonPTX.ObservedAccessShape', 'PoissonPTX.ObservedParallelExists', 'PoissonPTX.ObservedParallelPublication', 'PoissonPTX.ObservedPublication', 'PoissonPTX.ObservedReadWitness', 'PoissonPTX.ObservedWalk'])

COUNTS['PtxTorchLean.Poisson.PTX.Assembly.CompressedRows'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.CompressedRows', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Arena', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Arena.RowsEncoded'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Arena.RowsEncoded', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Assembly'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.MeshRows'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.MeshRows', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Rows'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Rows', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.Assembly.TableChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.TableChecks', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Execution'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Execution', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding', 0) + 8
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Family'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Family', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX'] = COUNTS.get('PtxTorchLean.Poisson.PTX', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.OperatorMesh'] = COUNTS.get('PtxTorchLean.Poisson.PTX.OperatorMesh', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.CellAssemblyWitness'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellAssemblyWitness', 0) + 40
TARGETS.update(['PoissonPTX.AssemblyCompressedRows', 'PoissonPTX.AssemblyRowRepresentation', 'PoissonPTX.AssemblyMeshRows', 'PoissonPTX.AssemblyTableConstruction', 'PoissonPTX.AssemblyOperator', 'PoissonPTX.AssemblyTableCheck', 'PoissonPTX.AssemblyTableChecks', 'PoissonPTX.CellExecution', 'PoissonPTX.CellTailPadding', 'PoissonPTX.CellExecutionStores', 'PoissonPTX.CellFamily', 'PoissonPTX.OperatorMesh', 'PoissonPTX.CellFamilyInputs', 'PoissonPTX.CellAssembly', 'PoissonPTX.CellAssemblyWitness', 'PoissonPTX.CellAssemblyChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Padding'] += 2

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.WordSourceCheck', 0) + 3
TARGETS.update(['PoissonPTX.SourceCheckWords'])

COUNTS['PtxTorchLean.Poisson.PTX.CellAssemblyWitness'] += 1

COUNTS['PtxTorchLean.Poisson.PTX.ArrayOperator'] = COUNTS.get('PtxTorchLean.Poisson.PTX.ArrayOperator', 0) + 20
COUNTS['PtxTorchLean.Poisson.PTX'] = COUNTS.get('PtxTorchLean.Poisson.PTX', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.ArrayOperator.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.ArrayOperator.Checks', 0) + 4
TARGETS.update(['PoissonPTX.OperatorArray', 'PoissonPTX.OperatorArrayRows', 'PoissonPTX.OperatorArrayCorrespondence', 'PoissonPTX.CellAssemblyReference', 'PoissonPTX.OperatorArrayChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.CellGrid'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid', 0) + 36
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Candidate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Candidate', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.Candidates'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.Candidates', 0) + 4
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.Admitted'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.Admitted', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.Checks', 0) + 13
TARGETS.update(['PoissonPTX.CellGrid', 'PoissonPTX.CellGridSources', 'PoissonPTX.CellGridPublication', 'PoissonPTX.CellGridFamily', 'PoissonPTX.CellCandidate', 'PoissonPTX.CellCandidateBounds', 'PoissonPTX.CellGridIndices', 'PoissonPTX.CellGridAdmission', 'PoissonPTX.CellGridExecution', 'PoissonPTX.CellGridInputs', 'PoissonPTX.CellGridAssembly', 'PoissonPTX.CellGridReference', 'PoissonPTX.CellGridChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.CellGrid'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid', 0) + 13
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Execution'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Execution', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellWhole.Family'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellWhole.Family', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.ExistsChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.ExistsChecks', 0) + 2
TARGETS.update(['PoissonPTX.CellGridSchedule', 'PoissonPTX.CellGridLiftSources', 'PoissonPTX.CellGridCandidates', 'PoissonPTX.CellGridExists', 'PoissonPTX.CellGridExistsChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Assembly.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Assembly.Arena', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.Admitted'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.Admitted', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.ResidualLayout'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.ResidualLayout', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.CellGrid.ResidualChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.CellGrid.ResidualChecks', 0) + 2
TARGETS.update(['PoissonPTX.AssemblyPreservation', 'PoissonPTX.CellGridResidualInputs', 'PoissonPTX.CellGridResidual', 'PoissonPTX.CellGridResidualChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderedSources'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderedSources', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.Checks', 0) + 20
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated.OrderChecks', 0) + 12
TARGETS.update(['PoissonPTX.RepeatedShared', 'PoissonPTX.RepeatedSharedChecks', 'PoissonPTX.RepeatedSharedOrderChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Reduction.Update'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Reduction.Update', 0) + 15
COUNTS['PtxTorchLean.Poisson.PTX.Reduction.Update.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Reduction.Update.Checks', 0) + 8
TARGETS.update(['PoissonPTX.ReductionUpdate', 'PoissonPTX.ReductionUpdateChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Witness', 0) + 34
TARGETS.update(['PoissonPTX.ReductionSources', 'PoissonPTX.ReductionStageSources', 'PoissonPTX.ReductionTreeWitness', 'PoissonPTX.ReductionTreeSources', 'PoissonPTX.ReductionTreeAdmission'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Limits'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Limits', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.AddressHold'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.AddressHold', 0) + 12
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control', 0) + 39
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Checks', 0) + 3
TARGETS.update(['PoissonPTX.ConcurrentLimits', 'PoissonPTX.ConcurrentAddressHold', 'PoissonPTX.ReductionControl', 'PoissonPTX.ReductionOwnership', 'PoissonPTX.ReductionPublication', 'PoissonPTX.ReductionReads', 'PoissonPTX.ReductionControlChecks'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Values'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Values', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric', 0) + 12
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Local'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Local', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Serial'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Serial', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256', 0) + 32
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256.Checks', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control', 0) + 3
TARGETS.update(['PoissonPTX.ConcurrentValues', 'PoissonPTX.ReductionNumerics', 'PoissonPTX.ReductionCorrect', 'PoissonPTX.ConcurrentLocalBlock', 'PoissonPTX.ConcurrentSerialLanes', 'PoissonPTX.ReductionLocal', 'PoissonPTX.ReductionWitnessWords', 'PoissonPTX.ReductionWitnessLayout', 'PoissonPTX.ReductionWaves', 'PoissonPTX.RepeatedSharedAdmission', 'PoissonPTX.ReductionWitnessAdmission', 'PoissonPTX.ReductionComplete', 'PoissonPTX.ReductionCompleteChecks', 'PoissonPTX.ReductionSafety'])

COUNTS['PtxTorchLean.Poisson.PTX.Flow.Boundary'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Boundary', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Flow.OperandWindow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.OperandWindow', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.DotInput'] = COUNTS.get('PtxTorchLean.Poisson.PTX.DotInput', 0) + 45
COUNTS['PtxTorchLean.Poisson.PTX.DotInput.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.DotInput.Checks', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Indexed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Indexed', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeGuard', 0) + 18
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native', 0) + 20
TARGETS.update(['PoissonPTX.ControlFlowBoundary', 'PoissonPTX.ControlFlowOperandWindow', 'PoissonPTX.ControlFlowOperandWindowExists', 'PoissonPTX.DotInputBody', 'PoissonPTX.DotInputChecks', 'PoissonPTX.DotInputComplete', 'PoissonPTX.DotInputExists', 'PoissonPTX.DotInputLayout', 'PoissonPTX.DotInputLoop', 'PoissonPTX.DotInputSetup', 'PoissonPTX.DotInputText', 'PoissonPTX.DotInputTraversal', 'PoissonPTX.IndexedScalar', 'PoissonPTX.NativeGuard', 'PoissonPTX.NativeGuardExists', 'PoissonPTX.NativeGuardInvariant', 'PoissonPTX.ReductionNative', 'PoissonPTX.ReductionNativeCode', 'PoissonPTX.ReductionNativeText'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot', 0) + 51
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow', 0) + 36
TARGETS.update(['PoissonPTX.DotAddress', 'PoissonPTX.DotAddressSyntax', 'PoissonPTX.DotAddressTail', 'PoissonPTX.DotCompletedInput', 'PoissonPTX.DotInputAccess', 'PoissonPTX.DotInputAdmitted', 'PoissonPTX.DotInputFootprint', 'PoissonPTX.DotInputObservations', 'PoissonPTX.DotProgram', 'PoissonPTX.DotProgramRegion', 'PoissonPTX.DotProgramText', 'PoissonPTX.DotStoreSyntax', 'PoissonPTX.DotStores', 'PoissonPTX.NativeFlow', 'PoissonPTX.NativeFlowFrame', 'PoissonPTX.NativeFlowOrigins', 'PoissonPTX.NativeFlowPrefix', 'PoissonPTX.NativeFlowPrefixComplete', 'PoissonPTX.NativeFlowRegion'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot', 0) + 28
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow', 0) + 13
TARGETS.update(['PoissonPTX.DotBarriers', 'PoissonPTX.DotPublicationAddress', 'PoissonPTX.DotPublicationRegisters', 'PoissonPTX.DotPublicationSafety', 'PoissonPTX.DotPublicationSyntax', 'PoissonPTX.DotPublicationTrack', 'PoissonPTX.DotPublicationValue', 'PoissonPTX.DotReturns', 'PoissonPTX.NativeFlowBarrier', 'PoissonPTX.NativeFlowDecompose', 'PoissonPTX.NativeFlowHalting', 'PoissonPTX.NativeFlowHistory', 'PoissonPTX.NativeFlowPrefixTrack'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot', 0) + 53
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot.Numeric', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow', 0) + 26
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Numeric', 0) + 7
TARGETS.update(['PoissonPTX.DotFinalRead', 'PoissonPTX.DotNumerics', 'PoissonPTX.DotOutputValue', 'PoissonPTX.DotSetupRegisters', 'PoissonPTX.DotStoreProtection', 'PoissonPTX.DotSuffixOrder', 'PoissonPTX.DotTreeAddress', 'PoissonPTX.DotTreeControl', 'PoissonPTX.DotTreeCorrect', 'PoissonPTX.DotTreeOwnership', 'PoissonPTX.DotTreeReads', 'PoissonPTX.DotTreeSources', 'PoissonPTX.NativeFlowAccessOrder', 'PoissonPTX.NativeFlowEventPrefix', 'PoissonPTX.NativeFlowInitialized', 'PoissonPTX.NativeFlowProducer', 'PoissonPTX.NativeFlowReadBarrier', 'PoissonPTX.NativeFlowStageSources', 'PoissonPTX.NativeFlowValues'])

COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness', 0) + 29
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness.Tail', 0) + 17
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.Repeated', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow', 0) + 11
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow.Serial', 0) + 6
TARGETS.update(['PoissonPTX.DotComplete', 'PoissonPTX.DotCompleteCandidate', 'PoissonPTX.DotInitialWave', 'PoissonPTX.DotInputRecorded', 'PoissonPTX.DotInputTreeCandidate', 'PoissonPTX.DotInputWave', 'PoissonPTX.DotOutputExists', 'PoissonPTX.DotStageWave', 'PoissonPTX.DotTailBody', 'PoissonPTX.DotTailGuard', 'PoissonPTX.DotTailLane', 'PoissonPTX.DotTailWave', 'PoissonPTX.DotTreeWitness', 'PoissonPTX.DotWitnessAdmission', 'PoissonPTX.DotWitnessGuard', 'PoissonPTX.DotWitnessLayout', 'PoissonPTX.DotWitnessProducers', 'PoissonPTX.DotWitnessWords', 'PoissonPTX.GlobalSharedAdmission', 'PoissonPTX.NativeFlowLayout', 'PoissonPTX.NativeFlowLocal', 'PoissonPTX.NativeFlowRound', 'PoissonPTX.NativeFlowSerial'])

COUNTS['PtxTorchLean.Poisson.PTX.AffineUpdate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.AffineUpdate', 0) + 18
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility.ThreadSourceChecks', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Concurrent.Visibility'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Concurrent.Visibility', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.ScalarLoad'] = COUNTS.get('PtxTorchLean.Poisson.PTX.ScalarLoad', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.VectorEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.VectorEntry', 0) + 5
TARGETS.update(['PoissonPTX.AffineUpdate', 'PoissonPTX.AffineUpdateCorrect', 'PoissonPTX.AffineUpdateEntry', 'PoissonPTX.AffineUpdateText', 'PoissonPTX.DecodedPublication', 'PoissonPTX.DotPublication', 'PoissonPTX.DotPublishedComplete', 'PoissonPTX.DotZeroReturn', 'PoissonPTX.GlobalThreadSourceChecks', 'PoissonPTX.GlobalThreadSources', 'PoissonPTX.ScalarLoad', 'PoissonPTX.VectorEntry'])

COUNTS['PtxTorchLean.Poisson.PTX.AffineUpdate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.AffineUpdate', 0) + 13
COUNTS['PtxTorchLean.Poisson.PTX.AffineUpdate.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.AffineUpdate.Arena', 0) + 21
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Parallel'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Parallel', 0) + 5
COUNTS['PtxTorchLean.Poisson.PTX.Flow.Observed'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow.Observed', 0) + 4
TARGETS.update(['PoissonPTX.AffineUpdateAccess', 'PoissonPTX.AffineUpdateAddress', 'PoissonPTX.AffineUpdateArena', 'PoissonPTX.AffineUpdateExists', 'PoissonPTX.AffineUpdateParallel', 'PoissonPTX.AffineUpdateRecorded', 'PoissonPTX.AffineUpdateSources', 'PoissonPTX.ObservedParallelNative', 'PoissonPTX.ObservedTemporalReplay'])

COUNTS['PtxTorchLean.Poisson.PTX.Flow'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Flow', 0) + 11
COUNTS['PtxTorchLean.Poisson.PTX.PreconditionUpdate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.PreconditionUpdate', 0) + 17
COUNTS['PtxTorchLean.Poisson.PTX.RegisterUpdate'] = COUNTS.get('PtxTorchLean.Poisson.PTX.RegisterUpdate', 0) + 15
COUNTS['PtxTorchLean.Poisson.PTX.UpdateXRZ'] = COUNTS.get('PtxTorchLean.Poisson.PTX.UpdateXRZ', 0) + 53
COUNTS['PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.UpdateXRZ.Arena', 0) + 38
COUNTS['PtxTorchLean.Poisson.PTX.UpdateXRZ.SameGeometry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.UpdateXRZ.SameGeometry', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.VectorFlowEntry'] = COUNTS.get('PtxTorchLean.Poisson.PTX.VectorFlowEntry', 0) + 5
TARGETS.update(['PoissonPTX.ControlFlowScalarSegments', 'PoissonPTX.ControlFlowSegments', 'PoissonPTX.PreconditionUpdate', 'PoissonPTX.PreconditionUpdateCorrect', 'PoissonPTX.RegisterUpdate', 'PoissonPTX.RegisterUpdateFrame', 'PoissonPTX.UpdateXRZ', 'PoissonPTX.UpdateXRZAccess', 'PoissonPTX.UpdateXRZAddress', 'PoissonPTX.UpdateXRZArena', 'PoissonPTX.UpdateXRZArenaSafety', 'PoissonPTX.UpdateXRZCorrect', 'PoissonPTX.UpdateXRZExists', 'PoissonPTX.UpdateXRZFootprint', 'PoissonPTX.UpdateXRZLayout', 'PoissonPTX.UpdateXRZMemory', 'PoissonPTX.UpdateXRZNumeric', 'PoissonPTX.UpdateXRZParallel', 'PoissonPTX.UpdateXRZParallelExists', 'PoissonPTX.UpdateXRZPending', 'PoissonPTX.UpdateXRZRecorded', 'PoissonPTX.UpdateXRZSources', 'PoissonPTX.UpdateXRZState', 'PoissonPTX.UpdateXRZText', 'PoissonPTX.VectorFlowEntry'])

COUNTS['PtxTorchLean.Poisson.PTX'] = COUNTS.get('PtxTorchLean.Poisson.PTX', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.ArrayArena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.ArrayArena', 0) + 14
COUNTS['PtxTorchLean.Poisson.PTX.DividePair'] = COUNTS.get('PtxTorchLean.Poisson.PTX.DividePair', 0) + 8
COUNTS['PtxTorchLean.Poisson.PTX.RestartVectors'] = COUNTS.get('PtxTorchLean.Poisson.PTX.RestartVectors', 0) + 40
COUNTS['PtxTorchLean.Poisson.PTX.RestartVectors.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.RestartVectors.Arena', 0) + 18
COUNTS['PtxTorchLean.Poisson.PTX.VectorCopy'] = COUNTS.get('PtxTorchLean.Poisson.PTX.VectorCopy', 0) + 8
TARGETS.update(['PoissonPTX.ArrayArena', 'PoissonPTX.ArrayArenaSafety', 'PoissonPTX.DividePair', 'PoissonPTX.RestartVectors', 'PoissonPTX.RestartVectorsAccess', 'PoissonPTX.RestartVectorsAddress', 'PoissonPTX.RestartVectorsArena', 'PoissonPTX.RestartVectorsCorrect', 'PoissonPTX.RestartVectorsEntry', 'PoissonPTX.RestartVectorsExists', 'PoissonPTX.RestartVectorsInputs', 'PoissonPTX.RestartVectorsParallel', 'PoissonPTX.RestartVectorsRecorded', 'PoissonPTX.RestartVectorsState', 'PoissonPTX.RestartVectorsText', 'PoissonPTX.VectorCopy'])

COUNTS['PtxTorchLean.Poisson.PTX.Initialize'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Initialize', 0) + 51
COUNTS['PtxTorchLean.Poisson.PTX.Initialize.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Initialize.Arena', 0) + 19
COUNTS['PtxTorchLean.Poisson.PTX.StorePair'] = COUNTS.get('PtxTorchLean.Poisson.PTX.StorePair', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.StoreZero'] = COUNTS.get('PtxTorchLean.Poisson.PTX.StoreZero', 0) + 6
TARGETS.update(['PoissonPTX.Initialize', 'PoissonPTX.InitializeAccess', 'PoissonPTX.InitializeAddress', 'PoissonPTX.InitializeArena', 'PoissonPTX.InitializeCorrect', 'PoissonPTX.InitializeEntry', 'PoissonPTX.InitializeExists', 'PoissonPTX.InitializeInputs', 'PoissonPTX.InitializeParallel', 'PoissonPTX.InitializePrefix', 'PoissonPTX.InitializeRecorded', 'PoissonPTX.InitializeState', 'PoissonPTX.InitializeText', 'PoissonPTX.InitializeValues', 'PoissonPTX.StorePair', 'PoissonPTX.StoreZero'])

COUNTS['PtxTorchLean.Poisson.PTX.Scalar'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar', 0) + 78
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Comparison'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Comparison', 0) + 1
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Checks', 0) + 11
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Norm'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Norm', 0) + 13
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.RestartFlag'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.RestartFlag', 0) + 6
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Text'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Text', 0) + 9
TARGETS.update(['PoissonPTX.ScalarDeterministic', 'PoissonPTX.ScalarEntry', 'PoissonPTX.ScalarExecution', 'PoissonPTX.ScalarExtras', 'PoissonPTX.ScalarExtrasChecks', 'PoissonPTX.ScalarFrames', 'PoissonPTX.ScalarMemory', 'PoissonPTX.ScalarNorm', 'PoissonPTX.ScalarRestartFlag', 'PoissonPTX.ScalarSegments', 'PoissonPTX.ScalarText'])

COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Alpha'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Alpha', 0) + 33
COUNTS['PtxTorchLean.Poisson.PTX.Scalar'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar', 0) + 7
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Field'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Field', 0) + 2
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Arena'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Arena', 0) + 19
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Beta'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Beta', 0) + 53
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Coefficient'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Coefficient', 0) + 37
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.ConditionalDivide'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.ConditionalDivide', 0) + 9
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Control'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Control', 0) + 8
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Checks'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Checks', 0) + 8
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Text'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Text', 0) + 3
COUNTS['PtxTorchLean.Poisson.PTX.Scalar.Start'] = COUNTS.get('PtxTorchLean.Poisson.PTX.Scalar.Start', 0) + 37
TARGETS.update(['PoissonPTX.ScalarAlpha', 'PoissonPTX.ScalarAlphaCorrect', 'PoissonPTX.ScalarAlphaValues', 'PoissonPTX.ScalarArena', 'PoissonPTX.ScalarArithmetic', 'PoissonPTX.ScalarBeta', 'PoissonPTX.ScalarBetaCorrect', 'PoissonPTX.ScalarBetaExists', 'PoissonPTX.ScalarBetaGuards', 'PoissonPTX.ScalarBetaSegments', 'PoissonPTX.ScalarBetaValues', 'PoissonPTX.ScalarCoefficientGuards', 'PoissonPTX.ScalarCoefficientInputs', 'PoissonPTX.ScalarConditionalDivide', 'PoissonPTX.ScalarControl', 'PoissonPTX.ScalarControlChecks', 'PoissonPTX.ScalarControlText', 'PoissonPTX.ScalarFlagFrames', 'PoissonPTX.ScalarStart', 'PoissonPTX.ScalarStartExists', 'PoissonPTX.ScalarStartPublication', 'PoissonPTX.ScalarStartResult', 'PoissonPTX.ScalarStartValues'])

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
        subprocess.run(["lake", "--no-cache", "env", "lean",
                        "../../formalization/checks/reciprocal-instruction-v2.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean",
                        "../../formalization/checks/exponential-instruction-v1.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PtxBinary32/ShiftedExpChecks.lean"],
                       cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PtxBinary32/MaximumChecks.lean"],
                       cwd=HERE, check=True)
        for check in ("NormalizeChecks", "SumTreeChecks", "SumChecks"):
            subprocess.run(["lake", "--no-cache", "env", "lean", f"PtxBinary32/{check}.lean"],
                           cwd=HERE, check=True)
        for check in ("SoftmaxMemoryChecks", "SoftmaxPipelineChecks", "UnaryPointwiseChecks", "SoftmaxParallelChecks"):
            subprocess.run(["lake", "--no-cache", "env", "lean", f"PtxBinary32/{check}.lean"],
                           cwd=HERE, check=True)
        for check in ("PointwiseDifferenceChecks", "SoftmaxBackwardDotChecks", "BackwardDotChecks",
                      "SoftmaxBackwardExecutionChecks", "SoftmaxBackwardChecks"):
            subprocess.run(["lake", "--no-cache", "env", "lean", f"PtxBinary32/{check}.lean"],
                           cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PtxHardwareDenseChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonQuadChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonResidualChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonPTX/Checks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonPTX/ParallelResidualChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonPTX/ContractionChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonPTX/SharedStoreChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonPTX/BarrierChecks.lean"], cwd=HERE, check=True)
        subprocess.run(["lake", "--no-cache", "env", "lean", "PoissonPTX/ProducerChecks.lean"], cwd=HERE, check=True)
        for module in ("CellMiddleChecks", "CellMiddleWitness", "CellMiddleInputs", "ConcurrentReplayChecks", "CellSymbolic", "CellMiddleNumericChecks", "CellFinalChecks", "CellConsumerProgram", "CellConsumerChecks", "CellCoefficientProgram", "ProjectionChecks", "CellTailProgram", "CellTailChecks", "CellTailWitnessSources", "CellTailShape", "CellTailAddressChecks", "CellPublicationChecks", "CellPrologueChecks", "CellGatherChecks", "CellEntryChecks", "CellEntryProducerChecks", "CellEntryVisibilityChecks", "CellEntryRebaseChecks", "CellEntryJointChecks", "CellWholeChecks", "CellWholeZero", "AssemblyChecks", "AssemblyEntryChecks", "AssemblyArenaChecks", "ObservedChecks", "AssemblyParallelChecks", "AssemblyTableChecks", "CellAssemblyWitness", "CellAssemblyChecks", "OperatorArrayChecks", "CellGridChecks", "CellGridExistsChecks", "CellGridResidualChecks", "RepeatedSharedChecks", "RepeatedSharedOrderChecks", "ReductionUpdateChecks", "ReductionTreeWitness", "ReductionTreeAdmission", "ReductionControlChecks", "ReductionCompleteChecks", "DotInputChecks"):
            subprocess.run(["lake", "--no-cache", "env", "lean", f"PoissonPTX/{module}.lean"], cwd=HERE, check=True)
        # Executable wrappers share global main; audit them in separate environments.
        for wrapper_file in ("PoissonQuadMain.lean", "PoissonResidualMain.lean", "PoissonPTXMain.lean", "PoissonContractionsMain.lean"):
            wrapper = subprocess.run(["lake", "--no-cache", "env", "lean", wrapper_file],
                                     cwd=HERE, check=True, text=True, stdout=subprocess.PIPE)
            audit_dependencies(wrapper.stdout, ["main"])
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
