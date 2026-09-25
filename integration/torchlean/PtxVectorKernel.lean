import PtxReluKernel
import PtxBinary32.Dot

/-! A serialized reference implementation of a vector ReLU neuron. The buffer
contains eight scalar slots followed by weights, inputs, dx and dw. -/
namespace PtxTorchLean.VectorKernel
open Ptx Ptx.Scalar Ptx.Scalar.Sequential Ptx.SequentialStorage
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Buffer (n : Nat) := Fin (8+4*n) → Word

def words (d : Buffer n) (tail : List Word) := List.ofFn d ++ tail

def slot (k : Fin 8) : Fin (8+4*n) := ⟨k.val,by omega⟩
def weight (i : Fin n) : Fin (8+4*n) := ⟨8+i,by omega⟩
def input (i : Fin n) : Fin (8+4*n) := ⟨8+n+i,by omega⟩
def dx (i : Fin n) : Fin (8+4*n) := ⟨8+2*n+i,by omega⟩
def dw (i : Fin n) : Fin (8+4*n) := ⟨8+3*n+i,by omega⟩

def pairs (d : Buffer n) := List.ofFn fun i : Fin n => (d (weight i),d (input i))

inductive Gradient (n : Nat) where
  | dx (i : Fin n) | dw (i : Fin n)
  deriving DecidableEq, Repr

def Gradient.source : Gradient n → Fin (8+4*n)
  | .dx i => weight i | .dw i => input i

def Gradient.dest : Gradient n → Fin (8+4*n)
  | .dx i => VectorKernel.dx i | .dw i => VectorKernel.dw i

inductive Stage (n : Nat) where
  | dot | bias | forward | gate | gradient (g : Gradient n)
  deriving DecidableEq, Repr

def Stage.dest : Stage n → Fin (8+4*n)
  | .dot => slot 0 | .bias => slot 3 | .forward => slot 4 | .gate => slot 6
  | .gradient g => g.dest

def Stage.args : Stage n → Fin 4 → Nat
  | .dot, i => match i.val with | 0 => 8 | 1 => 8+n | _ => 0
  | .bias, i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3
  | .forward, i => match i.val with | 0 => 3 | 1 => 3 | _ => 4
  | .gate, i => match i.val with | 0 => 3 | 1 => 5 | _ => 6
  | .gradient g, i => match i.val with | 0 => 6 | 1 => g.source.val | 2 => 7 | _ => g.dest.val

def Stage.program : Stage n → List Mixed.Instr
  | .dot => Dot.program
  | .forward | .gate => ReluGate.program
  | _ => Affine.program

def arguments (allocation : Nat) (stage : Stage n) (i : Fin 4) : Argument :=
  ⟨allocation,Dot.pointer (stage.args i)⟩

def registers (stage : Stage n) (seed : Seed) : Seed :=
  match stage with
  | .dot => {seed with regs := Ptx.Scalar.update seed.regs 3 (BitVec.ofNat 32 n)}
  | _ => seed

def stageStart (d : Buffer n) (tail : List Word) (allocation : Nat) (stage : Stage n) (seed : Seed) : State :=
  start (registers stage seed) (arguments allocation stage) (words d tail)

def request (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (seeds : Stage n → Seed) (stage : Stage n) : Request :=
  ⟨target,stage.program,thread,allocation,4,arguments allocation stage,registers stage (seeds stage)⟩

def Results (d : Buffer n) : Stage n → Word → Prop
  | .dot,v => Dot.Fold (pairs d) 0 v
  | .bias,v => ∃ p, Binary32.Error.AffineResults (d (slot 0)) (d (slot 1)) (d (slot 2)) p v
  | .forward,v => v = Binary32.Relu.forward (d (slot 3))
  | .gate,v => v = Binary32.Relu.gate (d (slot 3)) (d (slot 5))
  | .gradient g,v => ∃ p, Binary32.Error.AffineResults (d (slot 6)) (d g.source) (d (slot 7)) p v

inductive Evaluation : Buffer n → List (Stage n) → Buffer n → Prop
  | nil : Evaluation d [] d
  | cons : Results d stage v → Evaluation (Function.update d stage.dest v) rest out → Evaluation d (stage::rest) out

def forwardStages (n : Nat) : List (Stage n) := [.dot,.bias,.forward]
def gradients (n : Nat) : List (Gradient n) := (List.finRange n).flatMap fun i => [.dx i,.dw i]
def backwardStages (n : Nat) : List (Stage n) := [.dot,.bias,.gate] ++ (gradients n).map .gradient

@[simp] theorem words_length (d : Buffer n) (tail : List Word) : (words d tail).length = 8+4*n+tail.length := by simp [words]
@[simp] theorem words_get (d : Buffer n) (tail : List Word) (i : Fin (8+4*n)) :
    (words d tail)[i.val]? = some (d i) := by simp [words,List.getElem?_append,i.isLt]
@[simp] theorem words_getBang (d : Buffer n) (tail : List Word) (i : Fin (8+4*n)) :
    (words d tail)[i.val]! = d i := by simp [List.getElem!_eq_getElem?_getD]

theorem words_update (d : Buffer n) (tail : List Word) (i : Fin (8+4*n)) (v : Word) :
    (words d tail).set i.val v = words (Function.update d i v) tail := by
  apply List.ext_getElem?
  intro j
  by_cases h : j < 8+4*n
  · let k : Fin (8+4*n) := ⟨j,h⟩
    change ((words d tail).set i.val v)[k.val]? = (words (Function.update d i v) tail)[k.val]?
    by_cases e : k = i
    · rw [e]
      rw [List.getElem?_set_self (by simp; omega),words_get,Function.update_self]
    · have ne : i.val ≠ k.val := fun h => e (Fin.ext h.symm)
      simp [List.getElem?_set_ne ne,Function.update_of_ne e]
  · have ne : i.val ≠ j := by have := i.isLt; omega
    simp [words,List.getElem?_append,h]

private theorem pointer_nat (small : n < 2^32) (i : Nat) (bound : i ≤ 8+4*n) :
    (Dot.pointer i).toNat = 4*i := by
  have h : 4*i < 18446744073709551616 := by omega
  simp [Dot.pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h]

private theorem arg_bound (stage : Stage n) (notDot : stage ≠ .dot) (i : Fin 4) :
    stage.args i < 8+4*n := by
  cases stage with
  | dot => contradiction
  | gradient g => cases g <;> fin_cases i <;> simp [Stage.args,Gradient.source,Gradient.dest,weight,input,VectorKernel.dx,VectorKernel.dw] <;> omega
  | _ => fin_cases i <;> simp [Stage.args] <;> omega

private theorem valid_arg (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (stage : Stage n) (notDot : stage ≠ .dot) (i : Fin 4) :
    ValidAddress (words d tail) (Dot.pointer (stage.args i)) := by
  have h := arg_bound stage notDot i
  simp [ValidAddress,pointer_nat small (stage.args i) (by omega)]
  omega

private theorem affine_initial (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (notDot : stage ≠ .dot) :
    Affine.Initial (stageStart d tail allocation stage seed) := by
  refine ⟨rfl,?_⟩
  intro i
  simpa [stageStart,start,arguments] using valid_arg small d tail stage notDot i

private theorem gate_initial (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (notDot : stage ≠ .dot) :
    ReluGate.Initial (stageStart d tail allocation stage seed) := by
  refine ⟨rfl,?_⟩
  intro i
  have hi : i.val < 4 := by omega
  simpa [stageStart,start,arguments,hi] using valid_arg small d tail stage notDot ⟨i.val,hi⟩

private theorem affine_input (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (notDot : stage ≠ .dot) (i : Fin 3) :
    Affine.input (stageStart d tail allocation stage seed) i =
      d ⟨stage.args ⟨i.val,by omega⟩,arg_bound stage notDot _⟩ := by
  have h := arg_bound stage notDot ⟨i.val,by omega⟩
  have hi : i.val < 4 := by omega
  simpa [Affine.input,stageStart,start,arguments,hi,pointer_nat small (stage.args ⟨i.val,hi⟩) (by omega)] using
    words_getBang d tail ⟨stage.args ⟨i.val,by omega⟩,h⟩

private theorem affine_values (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (notDot : stage ≠ .dot) :
    Affine.input (stageStart d tail allocation stage seed) 0 = d ⟨stage.args 0,arg_bound stage notDot 0⟩ ∧
    Affine.input (stageStart d tail allocation stage seed) 1 = d ⟨stage.args 1,arg_bound stage notDot 1⟩ ∧
    Affine.input (stageStart d tail allocation stage seed) 2 = d ⟨stage.args 2,arg_bound stage notDot 2⟩ :=
  ⟨affine_input small d tail allocation stage seed notDot 0,
   affine_input small d tail allocation stage seed notDot 1,
   affine_input small d tail allocation stage seed notDot 2⟩

private theorem dot_bounds (small : n < 2^32) (d : Buffer n) (tail : List Word) :
    Dot.Bounds (words d tail) 8 (8+n) (pairs d) := by
  constructor <;> simp [pairs] <;> omega

private theorem dot_stored (d : Buffer n) (tail : List Word) :
    Dot.Stored (words d tail) 8 (8+n) (pairs d) := by
  intro i x hx
  obtain ⟨h,e⟩ := List.getElem?_eq_some_iff.mp hx
  simp only [pairs,List.length_ofFn] at h
  simp only [pairs,List.getElem_ofFn] at e
  subst x
  exact ⟨words_get d tail (weight ⟨i,h⟩),words_get d tail (input ⟨i,h⟩)⟩

private theorem dot_initial (d : Buffer n) (tail : List Word) (allocation : Nat) (seed : Seed) :
    Dot.initial (stageStart d tail allocation .dot seed) 8 (8+n) 0 (pairs d).length =
      stageStart d tail allocation .dot seed := by
  have ha : Ptx.Scalar.update (Ptx.Scalar.update (Ptx.Scalar.update
      (stageStart d tail allocation .dot seed).addrs 0 (Dot.pointer 8)) 1 (Dot.pointer (8+n)))
      2 (Dot.pointer 0) = (stageStart d tail allocation .dot seed).addrs := by
    funext i
    by_cases h0 : i = 0
    · subst i; simp [stageStart,start,registers,arguments,Stage.args,Scalar.update]
    by_cases h1 : i = 1
    · subst i; simp [stageStart,start,registers,arguments,Stage.args,Scalar.update]
    by_cases h2 : i = 2
    · subst i; simp [stageStart,start,registers,arguments,Stage.args,Scalar.update]
    simp [Scalar.update,h0,h1,h2]
  have hr : Ptx.Scalar.update (stageStart d tail allocation .dot seed).regs 3
      (BitVec.ofNat 32 (pairs d).length) = (stageStart d tail allocation .dot seed).regs := by
    funext i
    by_cases h : i = 3 <;> simp [stageStart,start,registers,Scalar.update,pairs,h]
  simp only [Dot.initial,ha,hr]
  rfl

private theorem affine_memory (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (p v : Word)
    (dest : stage.args 3 = stage.dest.val) :
    (Affine.finish (stageStart d tail allocation stage seed) p v).memory =
      words (Function.update d stage.dest v) tail := by
  simpa [Affine.finish,Affine.afterAdd,Affine.afterMultiply,Affine.afterBias,
    Affine.afterRight,Affine.afterLeft,Affine.outputIndex,stageStart,start,arguments,
    dest,pointer_nat small stage.dest.val (Nat.le_of_lt stage.dest.isLt)] using
      words_update d tail stage.dest v

private theorem gate_memory (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed)
    (gated : stage = .forward ∨ stage = .gate) :
    ∃ v, Results d stage v ∧ (ReluGate.finish (stageStart d tail allocation stage seed)).memory =
      words (Function.update d stage.dest v) tail := by
  have h3 : 3 < 8+4*n := by omega
  have h5 : 5 < 8+4*n := by omega
  rcases gated with rfl | rfl
  · refine ⟨Binary32.Relu.forward (d (slot 3)),rfl,?_⟩
    simpa [ReluGate.finish,ReluGate.input,stageStart,start,arguments,Stage.args,
      Dot.pointer,Stage.dest,slot,words,List.getElem?_append,List.getElem?_ofFn,h3,h5,Binary32.Relu.forward] using
      words_update d tail (slot 4) (Binary32.Relu.forward (d (slot 3)))
  · refine ⟨Binary32.Relu.gate (d (slot 3)) (d (slot 5)),rfl,?_⟩
    simpa [ReluGate.finish,ReluGate.input,stageStart,start,arguments,Stage.args,
      Dot.pointer,Stage.dest,slot,words,List.getElem?_append,List.getElem?_ofFn,h3,h5] using
      words_update d tail (slot 6) (Binary32.Relu.gate (d (slot 3)) (d (slot 5)))

theorem run_correct (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (eligible : Mixed.Eligible target)
    (run : Mixed.Run target stage.program (stageStart d tail allocation stage seed) final .halted events) :
    ∃ v, Results d stage v ∧ final.memory = words (Function.update d stage.dest v) tail := by
  cases stage with
  | dot =>
    have r := Dot.correct (output := 0) (s := stageStart d tail allocation .dot seed)
      (dot_bounds small d tail) (dot_stored d tail) (by simp [stageStart,start]) (by decide)
      (by rw [dot_initial]; exact run)
    obtain ⟨_,_,v,hv,hm⟩ := r
    exact ⟨v,hv,hm.trans (words_update d tail (slot 0) v)⟩
  | bias =>
    obtain ⟨p,v,hv,hf,_,_⟩ := (Affine.run_iff _ target
      (affine_initial small d tail allocation .bias seed (by simp)) eligible _ _ _).mp run
    refine ⟨v,⟨p,?_⟩,hf ▸ affine_memory small d tail allocation .bias seed p v rfl⟩
    obtain ⟨h0,h1,h2⟩ := affine_values small d tail allocation .bias seed (by simp)
    simpa [h0,h1,h2,Stage.args,slot] using hv
  | gradient g =>
    obtain ⟨p,v,hv,hf,_,_⟩ := (Affine.run_iff _ target
      (affine_initial small d tail allocation (.gradient g) seed (by simp)) eligible _ _ _).mp run
    refine ⟨v,⟨p,?_⟩,hf ▸ affine_memory small d tail allocation (.gradient g) seed p v rfl⟩
    obtain ⟨h0,h1,h2⟩ := affine_values small d tail allocation (.gradient g) seed (by simp)
    simpa [h0,h1,h2,Stage.args,slot] using hv
  | forward =>
    have hf := ((ReluGate.run_iff _ target (gate_initial small d tail allocation .forward seed (by simp))
      eligible final .halted).mp ⟨events,run⟩).1
    rw [hf]; exact gate_memory small d tail allocation .forward seed (Or.inl rfl)
  | gate =>
    have hf := ((ReluGate.run_iff _ target (gate_initial small d tail allocation .gate seed (by simp))
      eligible final .halted).mp ⟨events,run⟩).1
    rw [hf]; exact gate_memory small d tail allocation .gate seed (Or.inr rfl)

theorem run_exists (small : n < 2^32) (d : Buffer n) (tail : List Word)
    (allocation : Nat) (stage : Stage n) (seed : Seed) (eligible : Mixed.Eligible target) :
    ∃ final events, Mixed.Run target stage.program (stageStart d tail allocation stage seed) final .halted events := by
  cases stage with
  | dot =>
    obtain ⟨final,events,run,_,_⟩ := Dot.execution_exists (output := 0) (s := stageStart d tail allocation .dot seed)
      eligible (dot_bounds small d tail) (dot_stored d tail) (by simp [stageStart,start]) (by decide)
    exact ⟨final,events,by simpa only [dot_initial,Stage.program] using run⟩
  | bias => exact Affine.run_exists _ target (affine_initial small d tail allocation .bias seed (by simp)) eligible
  | gradient g => exact Affine.run_exists _ target (affine_initial small d tail allocation (.gradient g) seed (by simp)) eligible
  | forward =>
    obtain ⟨events,run⟩ := ReluGate.run_exists _ target (gate_initial small d tail allocation .forward seed (by simp)) eligible
    exact ⟨_,events,run⟩
  | gate =>
    obtain ⟨events,run⟩ := ReluGate.run_exists _ target (gate_initial small d tail allocation .gate seed (by simp)) eligible
    exact ⟨_,events,run⟩

variable {target : Target} {thread : ThreadLocation} {allocation : Nat} {registers : Stage n → Seed}
  {before after : Store} {d : Buffer n} {tail : List Word}

theorem launch_correct (small : n < 2^32) (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target)
    (launch : SuccessfulLaunch (request target thread allocation registers stage) before after final events) :
    ∃ v, Results d stage v ∧ after.cells allocation = some ⟨thread.device,words (Function.update d stage.dest v) tail⟩ := by
  obtain ⟨v,hv,hm⟩ := run_correct small d tail allocation stage (registers stage) eligible (launch.run_from present)
  exact ⟨v,hv, by simpa only [request, hm] using launch.writeback_lookup present⟩

theorem launch_exists (small : n < 2^32) (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target) (stage : Stage n) :
    ∃ after final events, SuccessfulLaunch (request target thread allocation registers stage) before after final events := by
  obtain ⟨final,events,run⟩ := run_exists small d tail allocation stage (registers stage) eligible
  obtain ⟨after,launch⟩ := Sequential.launch_exists
    (request := request target thread allocation registers stage) present rfl (fun _ => rfl) run
  exact ⟨after,final,events,launch⟩

theorem pipeline_correct (small : n < 2^32) (stages : List (Stage n))
    (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (stages.map (request target thread allocation registers)) after) :
    ∃ out, Evaluation d stages out ∧ after.cells allocation = some ⟨thread.device,words out tail⟩ := by
  induction stages generalizing before d with
  | nil => cases chain; exact ⟨d,.nil,present⟩
  | cons stage rest ih =>
    cases chain with
    | cons launch chain =>
      obtain ⟨v,hv,saved⟩ := launch_correct small present eligible launch
      obtain ⟨out,ev,saved'⟩ := ih saved chain
      exact ⟨out,.cons hv ev,saved'⟩

theorem pipeline_exists (small : n < 2^32) (stages : List (Stage n))
    (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target) :
    ∃ after, Chain before (stages.map (request target thread allocation registers)) after := by
  induction stages generalizing before d with
  | nil => exact ⟨before,.nil⟩
  | cons stage rest ih =>
    obtain ⟨middle,final,events,launch⟩ := launch_exists (registers := registers) small present eligible stage
    obtain ⟨v,_,saved⟩ := launch_correct small present eligible launch
    obtain ⟨after,chain⟩ := ih saved
    exact ⟨after,.cons launch chain⟩

/-- Every executed load/store is aligned and within the supplied allocation. -/
theorem launch_memory_safe (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (launch : SuccessfulLaunch (request target thread allocation registers stage) before after final events)
    (member : event ∈ events) (access : event.memory = some effect) :
    ValidAddress (words d tail) effect.address :=
  (launch.run_from present).memory_safe member access

/-- Executing these requests preserves every other allocation. -/
theorem pipeline_frame (stages : List (Stage n))
    (chain : Chain before (stages.map (request target thread allocation registers)) after)
    (other : Nat) (different : other ≠ allocation) : after.cells other = before.cells other := by
  induction stages generalizing before with
  | nil => cases chain; rfl
  | cons stage rest ih =>
    cases chain with
    | cons launch chain => exact (ih chain).trans (launch.other_cell different)


/-- Any word not written by a stage is preserved, including inputs and constants. -/
theorem Evaluation.frame (ev : Evaluation d stages out) (i : Fin (8+4*n))
    (untouched : ∀ stage ∈ stages, stage.dest ≠ i) : out i = d i := by
  induction ev with
  | nil => rfl
  | @cons d stage v rest out hv ev ih =>
    rw [ih (fun s hs => untouched s (by simp [hs]))]
    exact Function.update_of_ne (Ne.symm (untouched stage (by simp))) _ _

@[simp] theorem Gradient.source_ne_slot (g : Gradient n) (k : Fin 8) : g.source ≠ slot k := by
  cases g <;> simp [Gradient.source,weight,input,slot,Fin.ext_iff] <;> omega
@[simp] theorem Gradient.dest_ne_slot (g : Gradient n) (k : Fin 8) : g.dest ≠ slot k := by
  cases g <;> simp [Gradient.dest,VectorKernel.dx,VectorKernel.dw,slot,Fin.ext_iff] <;> omega
@[simp] theorem Gradient.source_ne_dest (g h : Gradient n) : g.source ≠ h.dest := by
  cases g <;> cases h <;> simp [Gradient.source,Gradient.dest,weight,input,VectorKernel.dx,VectorKernel.dw,Fin.ext_iff] <;> omega

theorem Gradient.dest_injective : Function.Injective (Gradient.dest (n := n)) := by
  intro g h e
  cases g <;> cases h <;> simp [Gradient.dest,VectorKernel.dx,VectorKernel.dw,Fin.ext_iff] at e
  all_goals first | (congr 1; apply Fin.ext; omega) | omega

/-- No stage writes a source array, even when a gradient stage is repeated. -/
theorem Evaluation.sources_frame (ev : Evaluation d stages out) (g : Gradient n) :
    out g.source = d g.source := by
  apply ev.frame
  intro stage _
  cases stage with
  | gradient h => exact Ne.symm (g.source_ne_dest h)
  | _ => exact Ne.symm (g.source_ne_slot _)

/-- Bias, seed, and the initialized constants survive both pipelines. -/
theorem Evaluation.constants_frame (ev : Evaluation d stages out) (k : Fin 8)
    (constant : k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 7) : out (slot k) = d (slot k) := by
  apply ev.frame
  intro stage _
  cases stage with
  | gradient g => exact g.dest_ne_slot k
  | _ => rcases constant with rfl | rfl | rfl | rfl <;> simp [Stage.dest,slot,Fin.ext_iff]

@[simp] theorem forward_launches : (forwardStages n).length = 3 := rfl
@[simp] theorem backward_launches : (backwardStages n).length = 3+2*n := by
  simp [backwardStages,gradients,List.length_flatMap]
  omega


private theorem eval_cons : Evaluation d (stage::rest) out ↔
    ∃ v, Results d stage v ∧ Evaluation (Function.update d stage.dest v) rest out := by
  constructor
  · intro h; cases h with | cons hv ht => exact ⟨_,hv,ht⟩
  · rintro ⟨v,hv,ht⟩; exact .cons hv ht
private theorem eval_nil : Evaluation d [] out ↔ out = d := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

private theorem gradient_results_update (d : Buffer n) (g h : Gradient n) (v out : Word) :
    Results (Function.update d h.dest v) (.gradient g) out ↔ Results d (.gradient g) out := by
  simp [Results,Function.update_of_ne,Ne.symm (h.dest_ne_slot 6),Ne.symm (h.dest_ne_slot 7)]

/-- Each coordinate result is derived from its own executed scalar multiplication. -/
theorem gradient_values (gs : List (Gradient n))
    (ev : Evaluation d (gs.map .gradient) out) (g : Gradient n) (member : g ∈ gs) :
    Results d (.gradient g) (out g.dest) := by
  induction gs generalizing d with
  | nil => simp at member
  | cons h rest ih =>
    obtain ⟨v,hv,ht⟩ := eval_cons.mp ev
    by_cases later : g ∈ rest
    · exact (gradient_results_update d g h v _).mp (ih ht later)
    · have eq : g = h := (List.mem_cons.mp member).resolve_right later
      subst h
      have same := ht.frame g.dest (by
        intro s hs
        obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hs
        intro e
        have eg : h = g := Gradient.dest_injective e
        exact later (eg ▸ hh))
      simpa [same,Stage.dest] using hv

theorem gradient_header {gs : List (Gradient n)} (ev : Evaluation d (gs.map Stage.gradient) out) (k : Fin 8) :
    out (slot k) = d (slot k) :=
  ev.frame _ (by
    intro stage hs
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hs
    exact g.dest_ne_slot k)

@[simp] theorem gradient_mem (g : Gradient n) : g ∈ gradients n := by
  cases g <;> simp [gradients,List.mem_flatMap]

/-- Forward arithmetic with the executed reduction order, before applying real-number bounds. -/
theorem forward_values (ev : Evaluation d (forwardStages n) out) :
    ∃ z p a, Dot.Fold (pairs d) 0 z ∧
      Binary32.Error.AffineResults z (d (slot 1)) (d (slot 2)) p a ∧
      out (slot 4) = Binary32.Relu.forward a := by
  simp only [forwardStages,eval_cons,eval_nil,Results,Stage.dest] at ev
  rcases ev with ⟨z,hz,a,⟨p,hp⟩,y,hy,rfl⟩
  refine ⟨z,p,a,hz,?_,?_⟩
  · simpa [slot] using hp
  · simpa [slot] using hy

/-- Backward recomputes its activation; all gradients come from actual launches. -/
theorem backward_values (ev : Evaluation d (backwardStages n) out) :
    ∃ z p a, Dot.Fold (pairs d) 0 z ∧
      Binary32.Error.AffineResults z (d (slot 1)) (d (slot 2)) p a ∧
      out (slot 6) = Binary32.Relu.gate a (d (slot 5)) ∧
      ∀ g : Gradient n, ∃ m,
        Binary32.Error.AffineResults (out (slot 6)) (d g.source) (d (slot 7)) m (out g.dest) := by
  simp only [backwardStages,List.cons_append,List.nil_append,eval_cons,Results,Stage.dest] at ev
  rcases ev with ⟨z,hz,a,⟨p,hp⟩,gate,hgate,ht⟩
  have header := gradient_header ht (6 : Fin 8)
  simp [slot] at hp hgate header
  refine ⟨z,p,a,hz,hp,header.trans hgate,?_⟩
  intro g
  have hv := gradient_values (gradients n) ht g (gradient_mem g)
  simp only [Results,Function.update_of_ne (g.source_ne_slot 0),
    Function.update_of_ne (g.source_ne_slot 3),Function.update_of_ne (g.source_ne_slot 6)] at hv
  simpa [header,hgate,slot] using hv

end PtxTorchLean.VectorKernel
