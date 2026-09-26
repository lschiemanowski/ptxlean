import PtxBinary32.GridDenseReadSources
import PtxBinary32.DenseData

namespace Ptx.Scalar.Parallel.GridDense
open Ptx.Scalar.Parallel.Dense
open Ptx.Binary32

private theorem pointer_injective (i j : Nat) (hi : i<2^32) (hj : j<2^32)
    (eq : bytePointer i=bytePointer j) : i=j := by
  have a : 4*i<18446744073709551616 := by omega
  have b : 4*j<18446744073709551616 := by omega
  have h := congrArg BitVec.toNat eq
  simp [bytePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b] at h
  omega

private theorem scratch_fits (s : Shape) (b : Dense.ArithmeticBounds s) (plane : Nat) (hp : plane≤s.depth) (t : Fin s.threads) :
    plane*s.threads+t.val<2^32 := by
  have ht := t.isLt
  have mul := Nat.mul_le_mul_right s.threads hp
  have bound := b.arithmetic
  dsimp [Shape.sharedWords] at bound
  rw [Nat.add_mul] at bound
  omega

/-- Same scratch address identifies both its stage and its supplying thread. -/
theorem scratch_pointer_owner (s : Shape) (b : Dense.ArithmeticBounds s) (p q : Nat) (hp : p≤s.depth) (hq : q≤s.depth)
    (t u : Fin s.threads) (same : bytePointer (p*s.threads+t.val)=bytePointer (q*s.threads+u.val)) : p=q ∧ t=u := by
  have eq := pointer_injective _ _ (scratch_fits s b p hp t) (scratch_fits s b q hq u) same
  have ht := t.isLt
  have hu := u.isLt
  have pos : 0<s.threads := by omega
  have indices := congrArg (· % s.threads) eq
  simp [Nat.add_mod,Nat.mod_eq_of_lt ht,Nat.mod_eq_of_lt hu] at indices
  have phases := Nat.mul_right_cancel pos (show p*s.threads=q*s.threads by omega)
  exact ⟨phases,Fin.ext indices⟩

/-- Turn the store-site certificate into its scratch-plane arithmetic contract. -/
theorem store_node (s : Shape) (global : List Word) (t : Fin s.threads) (plane pc : Nat) (value : Word)
    (hp : plane≤s.depth) (site : pc=sharedStorePC plane) (known : StoreData s global t pc value) :
    Node s global (t.val/s.width) plane (t.val%s.width) value := by
  cases plane with
  | zero => exact known.1 (by simpa [sharedStorePC] using site)
  | succ k => exact known.2.1 k hp (by simpa [sharedStorePC] using site)

/-- An actual shared read inherits the proved arithmetic contract of its
strictly earlier producer. The induction premise concerns past actual stores. -/
theorem shared_load_node (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (source co) (valid : Admitted s global seeds events source co)
    (q : Nat) (g : Fin s.rows) (reader : Fin s.width) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (g,.scalar reader (some .shared) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load)
    (past : ∀ p<q, ∀ (writer : Fin s.width) (so : Scalar.Occurrence) (stored : MemoryEffect),
      events[p]?=some (g,.scalar writer (some .shared) so) → so.memory=some stored → stored.kind=.store →
      StoreData s global (thread s g writer) so.pc stored.value)
    (plane : Nat) (hp : plane≤s.depth) (u : Fin s.threads)
    (address : effect.address=bytePointer (plane*s.threads+u.val)) :
    Node s global (u.val/s.width) plane (u.val%s.width) effect.value := by
  obtain ⟨p,writer,so,stored,atP,sm,sk,sa,value,before⟩ :=
    shared_read_source s b global seeds run halted source co valid q g reader occ effect atQ memory load
  obtain ⟨stage,hs,site,addr⟩ := candidate_shared_owner s b global seeds run g writer so stored (List.mem_of_getElem? atP) sm sk
  have eq : bytePointer (stage*s.threads+(thread s g writer).val)=bytePointer (plane*s.threads+u.val) := by rw [← addr,sa,address]
  obtain ⟨rfl,rfl⟩ := scratch_pointer_owner s b.arithmetic stage plane hs hp (thread s g writer) u eq
  rw [value]
  exact store_node s global (thread s g writer) _ so.pc stored.value hp site (past p before writer so stored atP sm sk)

private theorem child_coordinates (s : Dense.Shape) (k : Nat) (hk : k<s.depth) (t : Fin s.threads) (right : Bool)
    (active : t.val%s.width<2^(s.depth-(k+1))) :
    ∃ u : Fin s.threads, u.val/s.width=t.val/s.width ∧
      u.val%s.width=2*(t.val%s.width)+(if right then 1 else 0) ∧
      k*s.threads+u.val=leftIndex s k t+(if right then 1 else 0) := by
  obtain ⟨u,ua,index⟩ := Dense.child_owner s k hk t right active
  have children := children_bound s k (t.val%s.width) hk active
  have width : 2^(s.depth-k)≤s.width := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have small : 2*(t.val%s.width)+(if right then 1 else 0)<s.width := by cases right <;> simp <;> omega
  have eq : u.val=s.thread (t.val/s.width) (2*(t.val%s.width)+(if right then 1 else 0)) := by
    have coords := (coordinates s t).2.2
    dsimp [Shape.thread] at coords ⊢
    unfold leftIndex at index
    omega
  refine ⟨u,?_,?_,index⟩
  · simp [eq,Shape.thread,Nat.add_div,Nat.div_eq_of_lt small,Nat.mod_eq_of_lt small,Nat.not_le.mpr small,width_positive]
  · simp [eq,Shape.thread,Nat.add_mod,Nat.mod_eq_of_lt small]

/-- All load-value obligations for the next data-flow step follow from the full
run's admission and arithmetic facts already established for earlier stores. -/
theorem read_data (s : Dense.Shape) (b : Bounds s) (global : List Word)
    (seeds : Fin s.threads → Scalar.State) {events : List (Grid.Event s.rows s.width)} {final : Grid.State s.rows s.width}
    (run : Grid.Runs (config s b) (program s) (initial s global seeds) events final)
    (halted : ∀ g t, ((final.blocks g).lanes t).halted=true) (source co) (valid : Admitted s global seeds events source co)
    (q : Nat) (g : Fin s.rows) (reader : Fin s.width) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atQ : events[q]?=some (g,.scalar reader (some space) occ))
    (memory : occ.memory=some effect) (load : effect.kind=.load)
    (past : ∀ p<q, ∀ (writer : Fin s.width) (so : Scalar.Occurrence) (stored : MemoryEffect),
      events[p]?=some (g,.scalar writer (some .shared) so) → so.memory=some stored → stored.kind=.store →
      StoreData s global (thread s g writer) so.pc stored.value) : ReadData s global (thread s g reader) occ.pc effect.value := by
  have classified := candidate_load_address s b global seeds run g reader space occ effect (List.mem_of_getElem? atQ) memory load
  cases space with
  | global =>
    obtain ⟨i,hi,_,addr,value⟩ := global_read_source s b global seeds run source co valid q g reader occ effect atQ memory load
    have ifit : i<2^32 := by have := b.arithmetic.arithmetic; unfold Shape.globalWords at this; omega
    rcases classified with ⟨weight,site,_,active,role⟩ | ⟨_,_,_,_,sp,_⟩ | ⟨bias,site,sp,_,role⟩
    · have row := (coordinates s (thread s g reader)).1
      have wf : s.weight ((thread s g reader).val/s.width) ((thread s g reader).val%s.width)<2^32 := weight_index_fits s b.arithmetic (thread s g reader)
      have cf : (thread s g reader).val%s.width<2^32 := lt_trans (coordinates s (thread s g reader)).2.1 (width_fits s b.arithmetic)
      cases weight
      · have eq := pointer_injective _ _ ifit cf (addr.symm.trans role)
        subst i
        rw [value]
        unfold ReadData
        simp only [Bool.false_eq_true,↓reduceIte] at site
        constructor; intro _; rfl
        constructor; intro h; omega
        constructor; intro k hk h; omega
        constructor; intro k hk h; omega
        constructor; intro h; omega
        intro h; omega
      · have eq := pointer_injective _ _ ifit wf (addr.symm.trans role)
        subst i
        rw [value]
        unfold ReadData
        simp only [Bool.false_eq_true,↓reduceIte] at site
        constructor; intro h; omega
        constructor; intro _; rfl
        constructor; intro k hk h; omega
        constructor; intro k hk h; omega
        constructor; intro h; omega
        intro h; omega
    · cases sp
    · cases bias with
      | false => cases sp
      | true =>
        have bf : biasIndex s (thread s g reader)<2^32 := by have := (output_indices s (thread s g reader)).2.1; have := b.arithmetic.arithmetic; unfold Shape.globalWords at this; omega
        have eq := pointer_injective _ _ ifit bf (addr.symm.trans role)
        subst i
        rw [value]
        unfold ReadData
        simp only [↓reduceIte] at site
        unfold biasIndex
        constructor; intro h; omega
        constructor; intro h; omega
        constructor; intro k hk h; omega
        constructor; intro k hk h; omega
        constructor; intro h; omega
        intro _; congr 1 <;> omega
  | shared =>
    rcases classified with ⟨_,_,sp,_⟩ | ⟨k,hk,right,site,_,active,addr⟩ | ⟨bias,site,sp,leader,addr⟩
    · cases sp
    · obtain ⟨u,row,col,index⟩ := child_coordinates s k hk (thread s g reader) right active
      have node := shared_load_node s b global seeds run halted source co valid q g reader occ effect atQ memory load past k (by omega) u (by rw [addr,index])
      rw [row,col] at node
      cases right <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at node site
      all_goals
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        · intro h; omega
        · intro h; omega
        · intro j hj h; have eq : j=k := (by omega); subst j; first | exact node | omega
        · intro j hj h; have eq : j=k := (by omega); subst j; first | exact node | omega
        · intro h; omega
        · intro h; omega
    · cases bias with
      | true => cases sp
      | false =>
        have node := shared_load_node s b global seeds run halted source co valid q g reader occ effect atQ memory load past s.depth (Nat.le_refl _) (thread s g reader) (by simpa [rootIndex,Nat.add_comm] using addr)
        rw [leader] at node
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        · intro h; simp only [Bool.false_eq_true,↓reduceIte] at site; omega
        · intro h; simp only [Bool.false_eq_true,↓reduceIte] at site; omega
        · intro j hj h; simp only [Bool.false_eq_true,↓reduceIte] at site; omega
        · intro j hj h; simp only [Bool.false_eq_true,↓reduceIte] at site; omega
        · intro _; exact node
        · intro h; simp only [Bool.false_eq_true,↓reduceIte] at site; omega

end Ptx.Scalar.Parallel.GridDense
