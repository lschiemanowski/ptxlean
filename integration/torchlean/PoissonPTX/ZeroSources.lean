import PoissonPTX.CellWordView
import PoissonPTX.ConcurrentExec
import PoissonPTX.SymbolicRun

/-! Non-vacuity support for zero-data execution. This constructs witnesses for
Compatible/Performed only, not complete PTX memory admission or GPU progress. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources

/-- Search actual events for a whole-word store in the read's own space. -/
def writes (sp : Space) (address : Nat) : Event n → Bool
  | .data _ a => a.data.store && a.space==sp && a.data.address==address
  | _ => false

def source (events : List (Event n)) (r : Nat) (k : Fin 8) : Sources.Origin Nat :=
  match events[r]? with
  | some (.data _ a) =>
    let w := events.findIdx (writes a.space a.data.address)
    if w<events.length then .store w k else .initial
  | _ => .initial

def Zero (events : List (Event n)) : Prop :=
  ∀ thread a, Event.data thread a∈events → a.data.value=0

/-- Actual f64 load and store validity includes eight-byte alignment. -/
theorem aligned (run : Runs cfg program start events final)
    (member : Event.data thread access∈events) : access.data.address%8=0 := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  cases hd with
  | load valid => exact valid.2.1
  | store valid => exact valid.2.1

theorem compatible (zero : Zero events) : Visibility.Compatible (fun _ _ => 0) events (source events) := by
  intro r reader ra observed read k
  have rz := zero reader ra (List.mem_of_getElem? observed)
  simp only [source,observed]
  by_cases found : events.findIdx (writes ra.space ra.data.address)<events.length
  · simp only [found,ite_true]
    let w := events.findIdx (writes ra.space ra.data.address)
    have yes := List.findIdx_getElem (p:=writes ra.space ra.data.address) (xs:=events) (w:=found)
    have fetched : events[w]?=some events[w] := List.getElem?_eq_some_iff.mpr ⟨found,rfl⟩
    cases he : events[w] with
    | barrier => simp [w,he,writes] at yes
    | data writer wa =>
      have props : (wa.data.store=true ∧ wa.space=ra.space) ∧ wa.data.address=ra.data.address := by
        simpa [← show w=events.findIdx (writes ra.space ra.data.address) from rfl,he,writes] using yes
      have observedW : events[w]?=some (.data writer wa) := by simpa [he] using fetched
      refine ⟨writer,wa,observedW,props.1.1,props.1.2,by rw [props.2],?_⟩
      rw [rz,zero writer wa (List.mem_of_getElem? observedW)]
  · simp only [found,ite_false]
    rw [rz]
    change byte (0 : Word) k.val=0
    fin_cases k <;> decide +kernel

/-- Aligned overlap forces the same word start. Choosing a matching actual store
therefore excludes initialization whenever the barrier rule requires this. -/
theorem performed (run : Runs cfg program start events final) : Visibility.Performed events (source events) := by
  intro w r writer reader wa ra hw hr write read sw sr ordered j k same
  have aw := aligned run (List.mem_of_getElem? hw)
  have ar := aligned run (List.mem_of_getElem? hr)
  have hj := j.isLt; have hk := k.isLt
  have addr : wa.data.address=ra.data.address := by omega
  have found : events.findIdx (writes ra.space ra.data.address)<events.length := by
    apply List.findIdx_lt_length.mpr
    exact ⟨.data writer wa,List.mem_of_getElem? hw,by simp [writes,write,sw,sr,addr]⟩
  simp [source,hr,found]

open Symbolic

/-- Chosen zero loads are derived from the executable witness, without reducing
the entire computed store history in the kernel. -/
theorem evaluate_zero_reads (h : evaluate op s 0=some (next,access))
    (ha : access=some a) (read : a.data.store=false) : a.data.value=0 := by
  cases op with
  | load64 sp dst addr =>
    simp only [evaluate] at h
    split at h
    · cases Option.some.inj h; cases ha; rfl
    · simp at h
  | store64 sp addr src =>
    simp only [evaluate] at h
    split at h
    · cases Option.some.inj h; cases ha; simp at read
    · simp at h
  | _ =>
    simp only [evaluate,Option.map_eq_some_iff] at h
    obtain ⟨t,ht,eq⟩ := h
    cases eq
    simp at ha

theorem tick_zero_reads (h : tick cfg program (fun _ _ => 0) thread s=some out) :
    Reads (fun _ _ => 0) out.events := by
  unfold tick at h
  split at h
  · simp at h
  · cases fetch : program[(s.lanes thread).pc]? with
    | none => simp [fetch] at h
    | some i =>
      cases i with
      | data op =>
        cases ev : evaluate op (s.lanes thread) 0 with
        | none => simp only [fetch,bind,Option.bind,ev,reduceCtorEq] at h
        | some pair =>
          rcases pair with ⟨next,access⟩
          simp only [fetch,bind,Option.bind,ev,Option.some.injEq] at h
          subst out
          intro t a member read
          simp only [List.mem_map,Option.mem_toList] at member
          obtain ⟨a',ha,eq⟩ := member
          cases eq
          exact evaluate_zero_reads ev ha read
      | skip => simp [fetch] at h; subst out; intro t a member; simp at member
      | sync =>
        simp [fetch] at h; subst out
        intro t a member
        simp only [synchronize] at member
        split at member <;> simp_all

theorem execute_zero_reads (h : execute cfg program (fun _ _ => 0) schedule s=some out) :
    Reads (fun _ _ => 0) out.events := by
  induction schedule generalizing s out with
  | nil => simp only [execute,Option.some.injEq] at h; subst out; intro t a member; simp at member
  | cons thread rest ih =>
    cases hf : tick cfg program (fun _ _ => 0) thread s with
    | none => simp only [execute,hf,bind, Option.bind,reduceCtorEq] at h
    | some first =>
      cases hl : execute cfg program (fun _ _ => 0) rest first.state with
      | none => simp only [execute,hf,hl,bind, Option.bind, pure,reduceCtorEq] at h
      | some last =>
        simp only [execute,hf,hl,bind, Option.bind, pure,Option.some.injEq] at h
        subst out
        intro t a member read
        rcases List.mem_append.mp member with member|member
        · exact tick_zero_reads hf t a member read
        · exact ih hl t a member read

end PtxTorchLean.Poisson.PTX.Concurrent.ZeroSources
