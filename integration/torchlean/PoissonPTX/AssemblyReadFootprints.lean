import PoissonPTX.AssemblyReadFields
import PoissonPTX.ObservedWalk

namespace PtxTorchLean.Poisson.PTX.Assembly
open ObservedAddress

/-- An actual read lies in an allocated input field that is disjoint from the
whole output vector. Fields may be on either side of the output vector. -/
def Arena.InputRead (a : Arena n) (width location : Nat) : Prop :=
  ∃ field : Word, ∃ count k : Nat,
    location=a.base.toNat+field.toNat+k*width ∧ k<count ∧ a.FieldApart field (count*width)

variable {n : Nat} {a : Arena n} {memory : Memory} {regs : Fin n → Registers}
  {t : Fin n → Flow.State} {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

/-- Read footprints are derived from actual control flow and one joint index
source assignment. Offset values establish loop bounds; contribution-index
values then establish the element-read bound. No floating-point read value or
separately supplied local execution is assumed. -/
theorem Arena.read_footprints
    (run : Flow.Parallel.Runs a.context
      (entryCode (BitVec.ofNat 32 n) a.offsets a.entries a.element mask a.boundary a.output)
      (fun i => a.start memory (regs i)) words indices t)
    (compatible : IndexSources.Compatible memory words indices indexSource)
    (contents : a.Contents memory) (separated : a.InputSeparation) (thread : Fin n) :
    (∀ read∈Flow.Parallel.wordsFor thread words, read.data.store=false →
      read.space=.global ∧ a.InputRead 8 read.data.address) ∧
    (∀ read∈Flow.Parallel.indicesFor thread indices, a.InputRead 4 read.address) := by
  let P : Flow.State → Prop := fun s =>
    Ready (a.context thread) mask a.output s ∧
    BoundsReady (a.offset memory (thread.val+1)) s ∧
    ReadAddressReady (a.context thread) a.entries a.element mask a.boundary s ∧
    IndexReady a.elementCount s
  have start : P (a.start memory (regs thread)) :=
    ⟨initial rfl,bounds_initial rfl,read_address_initial rfl,ObservedAddress.index_initial rfl⟩
  have checked := Flow.Observed.walk (P:=P)
    (W:=fun read => read.data.store=false → read.space=.global ∧ a.InputRead 8 read.data.address)
    (I:=fun read => a.InputRead 4 read.address)
    (Flow.Parallel.project run thread) (fun _ h => h) (fun _ h => h) start
  apply And.right (checked ?_)
  intro s next access indexRecord step wordMember indexMember state
  rcases state with ⟨launch,bounds,addresses,indexBound⟩
  have indexObserved : ∀ read, indexRecord=some read → (thread,read)∈indices :=
    fun read eq => Flow.Parallel.index_member.mp (indexMember read eq)
  have offsets : ∀ read, indexRecord=some read →
      (read.pc=9 → read.value.toNat=a.offset memory thread.val) ∧
      (read.pc=14 → read.value.toNat=a.offset memory (thread.val+1)) := by
    intro read eq
    constructor
    · intro pc
      simpa using a.offset_source (next:=false) run compatible separated (indexObserved read eq) pc
    · intro pc
      simpa using a.offset_source (next:=true) run compatible separated (indexObserved read eq) pc
  have indexValues : ∀ read, indexRecord=some read → read.pc=21 → read.value.toNat<a.elementCount := by
    intro read eq pc
    have stepRead := step
    rw [eq] at stepRead
    obtain ⟨inside,located⟩ := a.loop_index_field stepRead pc contents bounds addresses
    have value := a.index_initial run compatible (indexObserved read eq) located inside separated.entries
    rw [value,located]
    exact contents.indices _ inside
  refine ⟨⟨step_ready step launch,
    bounds_step step bounds (contents.ordered thread.val thread.isLt)
      (lt_of_le_of_lt (contents.last thread.val thread.isLt) a.entriesSmall) offsets,
    read_address_step step launch addresses,index_step step indexBound indexValues⟩,?_,?_⟩
  · intro read eq load
    have stepRead := step
    rw [eq] at stepRead
    obtain ⟨global,k,inside,located⟩ := a.element_field stepRead load indexBound addresses
    exact ⟨global,a.element,a.elementCount,k,located,inside,separated.element⟩
  · intro read eq
    have stepRead := step
    rw [eq] at stepRead
    obtain ⟨atPC,_,sites⟩ := index_site stepRead
    rcases sites with first | second | entry | ⟨enabled,boundary⟩
    · have located := a.offset_record (next:=false) run (indexObserved read eq) (atPC.trans first)
      exact ⟨a.offsets,n+1,thread.val,by simpa using located,by omega,separated.offsets⟩
    · have located := a.offset_record (next:=true) run (indexObserved read eq) (atPC.trans second)
      exact ⟨a.offsets,n+1,thread.val+1,by simpa using located,by have := thread.isLt; omega,separated.offsets⟩
    · obtain ⟨inside,located⟩ := a.loop_index_field stepRead (atPC.trans entry) contents bounds addresses
      exact ⟨a.entries,a.entryCount,cursor s.core,located,inside,separated.entries⟩
    · exact ⟨a.boundary,n,thread.val,a.boundary_field stepRead (atPC.trans boundary) enabled addresses,
        thread.isLt,separated.boundary⟩

end PtxTorchLean.Poisson.PTX.Assembly
