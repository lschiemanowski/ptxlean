# A squared-affine computation across two kernels

This example connects the actual TorchLean scalar computation `(x*weight+bias)^2`
to two separately launched kernels. The first kernel multiplies x and weight,
rounds, adds bias, rounds again, and stores an intermediate word. The second
loads that stored word twice, multiplies and rounds, then explicitly adds positive
zero and rounds before storing the output. It reuses the affine kernel contract;
the final addition is part of the actual implementation and is not silently
replaced by a fused or ideal operation.

The five initial arena words hold x, weight, bias, arbitrary old intermediate
bits, and positive-zero bits. The first launch uses byte offsets 0, 4, 8 and 12.
The second uses 12, 12, 16 and 16: its two inputs alias the saved intermediate,
and its bias aliases its output. Both loads precede the final store. Extra arena
words remain unchanged. Each launch starts at program counter zero with its own
arbitrary supplied registers and predicates and explicit address arguments.
Only the live memory snapshot is carried between launches.

Every successful serialized two-launch execution must have the two actual
seven-instruction traces and the corresponding intermediate and final words.
Those words satisfy the original binary32 result relations at every arithmetic
step. An execution exists for all initial input bit patterns, under the stated
live-allocation, device, argument and target conditions. Finite-input accuracy
has stronger input-only range and representation-error conditions; existence
does not imply a finite numerical answer.

The numerical guarantee concerns the actual output word in final memory and
compares its finite real value with the output of the actual pinned TorchLean
graph. It derives the rounded intermediate from the initial operands, propagates
its error through squaring, and accounts for all four explicit roundings.
It does not assume that either kernel returned a desired value or that a
second-stage output was finite. Bitwise agreement with PyTorch and derivatives
of a rounded machine execution are different claims.

The serialized launch contract supplies allocation identity, lifetime and the
handoff of completed memory to the next launch. Correspondence to a real runtime
requires completion, visibility and exclusion of interfering accesses; PTX thread
exit alone does not prove that contract. Each kernel's local memory witness uses
its own entry snapshot. This does not construct a combined cross-kernel PTX
memory graph. The example uses initialized, aligned, whole-word global storage,
explicit nearest-even binary32 arithmetic and ISA 9.4 with the numeric sm_70+
feature boundary. It has no asynchronous work, host-pointer translation or
launch-ABI implementation.

TorchLean constructs the exact real backward computation for this graph
separately. This forward example supplies no PTX backward implementation or
proof. Its explanations distinguish exact real network meaning, numerical
accuracy, instruction execution and runtime correspondence.
