# TorchLean and kernel verification interface

The interface connects a neural-network specification expressed in TorchLean
to the GPU kernels implementing it, including computations split across several
kernels. A tensor is a multidimensional array of values. Its logical indices,
such as row and column, are related to the actual memory locations holding those
values; this relationship is its layout. The interface also relates state kept
between calls, temporary intermediate values, and computations using several
number formats, called mixed precision.

Two separate proofs are needed: that memory holds the intended tensor elements,
and that the numbers computed meet the accuracy requirements. A kernel contract
states what must hold on entry (its preconditions), the computation to perform,
and what is guaranteed on return. Different layouts, execution schedules, or
fusion choices can implement that contract. Fusion means combining computations
that could otherwise run in separate kernels.

Orchestration means coordinating several kernels. Its contracts describe reserving
memory, launching kernels, ensuring that inputs are ready before use, keeping
storage alive while needed, and identifying the resulting observable values.

Numerical contracts distinguish an ideal calculation over real numbers from
floating-point calculation, which uses finitely many representable values and
rounds results. They bound the resulting error and state the relationship to a
specific PyTorch implementation, rather than assuming the two computations are
identical.

A backward computation propagates sensitivities of a network's outputs back to
its inputs and parameters: it computes derivatives needed, for example, in
training. TorchLean constructs the backward specification automatically; the
PTX backward implementation and its correctness proof are supplied separately.

When one kernel produces data for another, its guarantees must satisfy the next
kernel's preconditions. This includes which threads may use the storage, how
long it remains allocated, the ordering needed to observe the writes, and the
numerical accuracy promised. Network-level proofs combine these contracts
without repeating instruction-level reasoning for every kernel connection.

Interface explanations show how a logical tensor relates to stored values,
which obligations change with a layout or precision choice, and how individual
kernel guarantees combine into a network-level claim. They identify the exact
TorchLean definitions and the hypotheses used in each correspondence theorem.
