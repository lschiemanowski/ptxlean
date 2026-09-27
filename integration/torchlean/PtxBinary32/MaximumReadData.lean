import PtxBinary32.MaximumData
import PtxBinary32.MaximumGlobalReads

namespace Ptx.Scalar.Parallel.Maximum
open Ptx.Binary32

private theorem pointer_injective (i j : Nat) (hi : i<2^32) (hj : j<2^32)
    (eq : bytePointer i=bytePointer j) : i=j := by
  have a : 4*i<18446744073709551616 := by omega
  have b : 4*j<18446744073709551616 := by omega
  have h := congrArg BitVec.toNat eq
  simp [bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b] at h
  omega

private theorem scratch_fits (d : Nat) (b : Bounds d) (plane : Nat) (hp : plane≤d) (t : Fin (width d)) :
    plane*(width d)+t.val<2^32 := by
  exact lt_trans (plane_bound d plane t.val hp t.isLt) (shared_fits b)

/-- Same scratch address identifies both its stage and its supplying thread. -/
theorem scratch_pointer_owner (d : Nat) (b : Bounds d) (p q : Nat) (hp : p≤d) (hq : q≤d)
    (t u : Fin (width d)) (same : bytePointer (p*(width d)+t.val)=bytePointer (q*(width d)+u.val)) : p=q ∧ t=u := by
  have eq := pointer_injective _ _ (scratch_fits d b p hp t) (scratch_fits d b q hq u) same
  have ht := t.isLt
  have hu := u.isLt
  have pos : 0<(width d) := by omega
  have indices := congrArg (· % (width d)) eq
  simp [Nat.add_mod,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hu] at indices
  have phases := Nat.mul_right_cancel pos (show p*(width d)=q*(width d) by omega)
  exact ⟨phases,Fin.ext indices⟩

/-- Turn the store-site certificate into its scratch-plane arithmetic contract. -/
theorem store_node (d : Nat) (global : List Word) (t : Fin (width d)) (plane pc : Nat) (value : Word)
    (hp : plane≤d) (site : pc=sharedStorePC plane) (known : StoreData d global t pc value) :
    value=node global plane t.val := by
  cases plane with
  | zero => simpa [node,Ptx.Binary32.Maximum.Tree.nodeValue] using known.1 (by simpa [sharedStorePC] using site)
  | succ k => exact known.2.1 k hp (by simpa [sharedStorePC] using site)

/-- An actual shared read inherits the proved arithmetic contract of its
strictly earlier producer. The induction premise concerns past actual stores. -/
theorem shared_load_node (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d) → Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted d b global shared seeds run source co)
    (q : Nat) (reader : Fin (width d)) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (.scalar reader (some .shared) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load)
    (past : ∀ p<q, ∀ (writer : Fin (width d)) (so : Scalar.Occurrence) (stored : MemoryEffect),
      events[p]?=some (.scalar writer (some .shared) so) → so.memory=some stored → stored.kind=.store →
      StoreData d global writer so.pc stored.value)
    (plane : Nat) (hp : plane≤d) (u : Fin (width d))
    (address : effect.address=bytePointer (plane*(width d)+u.val)) :
    effect.value=node global plane u.val := by
  obtain ⟨p,writer,so,stored,atP,sm,sk,sa,value,before⟩ :=
    shared_read_source d b global shared seeds run halted source co valid q reader occ effect atQ memory load
  obtain ⟨stage,hs,site,addr⟩ := candidate_shared_owner d b global shared seeds run writer so stored (List.mem_of_getElem? atP) sm sk
  have eq : bytePointer (stage*(width d)+writer.val)=bytePointer (plane*(width d)+u.val) := by rw [← addr,sa,address]
  obtain ⟨rfl,rfl⟩ := scratch_pointer_owner d b stage plane hs hp writer u eq
  rw [value]
  exact store_node d global writer _ so.pc stored.value hp site (past p before writer so stored atP sm sk)

/-- Each actual load is determined from admission and already justified stores. -/
theorem read_data (d : Nat) (b : Bounds d) (global shared : List Word)
    (seeds : Fin (width d)→Scalar.State) {events : List (Event (width d))} {final : Parallel.State (width d)}
    (run : Runs (config d) (program d) (initial d global shared seeds) events final)
    (halted : ∀ t, (final.lanes t).halted=true) (source co) (valid : Admitted d b global shared seeds run source co)
    (q : Nat) (reader : Fin (width d)) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (.scalar reader (some space) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load)
    (past : ∀ p<q, ∀ (writer : Fin (width d)) (so : Scalar.Occurrence) (stored : MemoryEffect),
      events[p]?=some (.scalar writer (some .shared) so) → so.memory=some stored → stored.kind=.store →
      StoreData d global writer so.pc stored.value) : ReadData d global reader occ.pc effect.value := by
  have classified := candidate_load_address d b global shared seeds run reader space occ effect (List.mem_of_getElem? atQ) memory load
  cases space with
  | global =>
    rcases classified with ⟨site,_,addr⟩ | ⟨_,_,_,_,sp,_⟩ | ⟨_,sp,_⟩
    · obtain ⟨i,hi,_,addr',value⟩ := global_read_source d b global shared seeds run source co valid q reader occ effect atQ memory load
      have same := pointer_injective i reader.val (lt_trans hi (width_fits b)) (lt_trans reader.isLt (width_fits b)) (addr'.symm.trans addr)
      subst i
      refine ⟨fun _ => value,?_,?_,?_⟩
      · intro k hk h; omega
      · intro k hk h; omega
      · intro h; omega
    · cases sp
    · cases sp
  | shared =>
    rcases classified with ⟨_,sp,_⟩ | ⟨k,hk,right,site,_,active,addr⟩ | ⟨site,_,leader,addr⟩
    · cases sp
    · obtain ⟨u,ua,index⟩ := child_owner d k hk reader right active
      have value := shared_load_node d b global shared seeds run halted source co valid q reader occ effect atQ memory load past k (by omega) u (by rw [addr,index])
      have coord : u.val=2*reader.val+(if right then 1 else 0) := by omega
      rw [coord] at value
      cases right <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at value site
      all_goals
        refine ⟨?_,?_,?_,?_⟩
        · intro h; omega
        · intro j hj h; have eq : j=k := (by omega); subst j; first | exact value | omega
        · intro j hj h; have eq : j=k := (by omega); subst j; first | exact value | omega
        · intro h; omega
    · have value := shared_load_node d b global shared seeds run halted source co valid q reader occ effect atQ memory load past d (Nat.le_refl _) reader (by simpa [leader] using addr)
      rw [leader] at value
      refine ⟨?_,?_,?_,fun _ => value⟩
      · intro h; omega
      · intro j hj h; omega
      · intro j hj h; omega
end Ptx.Scalar.Parallel.Maximum
