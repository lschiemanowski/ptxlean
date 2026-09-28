import PoissonPTX.Kernel

namespace PtxTorchLean.Poisson.PTX.Kernel.Residual

/-- The prologue emitted by PTX.entry and PTX.vector_start. -/
def prologue (count : BitVec 32) : List Instr :=
  [.parameter 0,.lane 14,.group 15,.mad32 12 15 256 14,.ge32 12 count,.predRet]

def program (count : BitVec 32) (rhs ap output : Word) : List Instr :=
  prologue count ++ (PTX.Residual.code rhs ap output).map Instr.data ++ [.ret]

def index (ctx : Context) : BitVec 32 := ctx.group*256+ctx.lane

def setup (ctx : Context) (s : State) (count : BitVec 32) : State :=
  simple ctx .predRet (simple ctx (.ge32 12 count)
    (simple ctx (.mad32 12 15 256 14) (simple ctx (.group 15)
      (simple ctx (.lane 14) (simple ctx (.parameter 0) s)))))

def live (ctx : Context) (count : BitVec 32) : Prop := (index ctx).toNat < count.toNat

@[simp] theorem setup_live (hl : live ctx count) (h : s.halted = false) :
    (setup ctx s count).halted = false := by
  have hn := Nat.not_le_of_lt hl
  simp only [live,index,BitVec.toNat_add,BitVec.toNat_mul] at hn
  norm_num at hn
  have hnneg := Nat.not_le_of_lt hn
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance,u32,hnneg,h]

@[simp] theorem setup_global : (setup ctx s count).core.global = s.core.global := by
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance]; split <;> rfl
@[simp] theorem setup_shared : (setup ctx s count).core.shared = s.core.shared := by
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance]; split <;> rfl
@[simp] theorem setup_bytes : (setup ctx s count).core.globalBytes = s.core.globalBytes := by
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance]; split <;> rfl

@[simp] theorem setup_start : (setup ctx s count).core.globalStart = s.core.globalStart := by
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance]; split <;> rfl

/-- The register index calculation is modular, exactly like mad.lo.u32.
Launch bounds below separately establish that it does not wrap. -/
@[simp] theorem setup_index : (setup ctx s count).core.regs 12 = (index ctx).setWidth 64 := by
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance,u32,index]; split <;> rfl
@[simp] theorem setup_base : (setup ctx s count).core.regs 0 = ctx.arena := by
  simp [setup,simple,scalar,advance,halt,assign,PTX.advance]; split <;> rfl

theorem index_exact (ctx : Context) (bound : ctx.group.toNat*256+ctx.lane.toNat < 2^32) :
    (index ctx).toNat = ctx.group.toNat*256+ctx.lane.toNat := by
  simp only [index,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat]
  norm_num
  omega

/-- Executing the ordinary prologue preserves arbitrary initial memory and
reaches the data instructions exactly when this thread is inside the vector. -/
theorem prologue_live (hl : live ctx count) (running : s.halted = false) :
    Exec ctx (prologue count ++ tail) s final ↔ Exec ctx tail (setup ctx s count) final := by
  have hn := Nat.not_le_of_lt hl
  simp only [live,index,BitVec.toNat_add,BitVec.toNat_mul] at hn
  norm_num at hn
  have hnneg := Nat.not_le_of_lt hn
  simp only [prologue,List.cons_append,List.nil_append]
  repeat rw [exec_nonhalting_iff (by simp)
    (by simp [simple,scalar,advance,halt,assign,PTX.advance,u32,hnneg,running])
    (by simp [simple,scalar,advance,halt,assign,PTX.advance,u32,hnneg,running])]
  rfl

/-- Full active-thread correctness. The inputs are read from initial bytes;
only alignment/allocation validity, launch input, and execution are premises. -/
theorem correct (ctx : Context) (s final : State) (count : BitVec 32) (rhs ap output : Word)
    (running : s.halted = false) (hl : live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 output).toNat)
    (execution : Exec ctx (program count rhs ap output) s final) :
    decode (read64 final.core.global (address (setup ctx s count).core 12 output).toNat) =
      decode (read64 s.core.global (address (setup ctx s count).core 12 rhs).toNat) -
      decode (read64 s.core.global (address (setup ctx s count).core 12 ap).toNat) ∧
    final.halted = true := by
  have hb := (prologue_live hl running).mp (by simpa [program,List.append_assoc] using execution)
  obtain ⟨middle,hbody,hret⟩ := exec_block hb
  have runMiddle : ({setup ctx s count with core := middle} : State).halted = false := setup_live hl running
  have hend := (exec_ordinary_iff (i := .ret) (by simp) runMiddle).mp hret
  rcases hend with ⟨eq,stopped⟩ | ⟨impossible,_⟩
  · subst final
    have h := PTX.Residual.correct _ _ rhs ap output
      (by simpa using hr) (by simpa using ha) (by simpa using ho) hbody
    simpa [simple,halt,advance,PTX.advance,PTX.Residual.result] using And.intro h.1 (show true = true from rfl)
  · simp [simple,halt] at impossible

theorem execution_exists (ctx : Context) (s : State) (count : BitVec 32) (rhs ap output : Word)
    (running : s.halted = false) (hl : live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 output).toNat) :
    ∃ final, Exec ctx (program count rhs ap output) s final := by
  let start := setup ctx s count
  let last := PTX.Residual.finish start.core rhs ap output (encode (PTX.Residual.result start.core rhs ap))
  have hbody := PTX.Residual.executes start.core rhs ap output
    (by simpa [start] using hr) (by simpa [start] using ha) (by simpa [start] using ho)
  let beforeReturn : State := {start with core := last}
  have hret : Exec ctx [.ret] beforeReturn (halt beforeReturn) :=
    .stop (setup_live hl running) (.simple (by simp)) rfl
  refine ⟨halt beforeReturn,?_⟩
  apply (prologue_live hl running).mpr
  exact block_exec hbody (setup_live hl running) hret

theorem prologue_inactive (hn : ¬ live ctx count) (running : s.halted = false) :
    Exec ctx (prologue count ++ tail) s final ↔ final = setup ctx s count := by
  have hge : count.toNat ≤ (index ctx).toNat := Nat.le_of_not_gt hn
  simp [index] at hge
  simp only [prologue,List.cons_append,List.nil_append]
  iterate 5 rw [exec_nonhalting_iff (by simp)
    (by simp [simple,scalar,advance,assign,PTX.advance,running])
    (by simp [simple,scalar,advance,assign,PTX.advance,running])]
  rw [exec_halting_iff (by simp)
    (by simp [simple,scalar,advance,assign,PTX.advance,running])
    (by simp [simple,scalar,advance,halt,assign,PTX.advance,u32,hge])]
  rfl

/-- Inactive lanes return without accessing or modifying data memory. -/
theorem inactive (execution : Exec ctx (program count rhs ap output) s final)
    (hn : ¬ live ctx count) (running : s.halted = false) :
    final.core.global = s.core.global ∧ final.core.shared = s.core.shared := by
  have he := (prologue_inactive hn running).mp (by simpa [program,List.append_assoc] using execution)
  subst final
  exact ⟨setup_global,setup_shared⟩

/-- The universal endpoint is about every completed fetched run of the full
kernel, including parameter/builtin loads, indexing, guard and return. -/
theorem fetched_correct (ctx : Context) (s final : State) (count : BitVec 32) (rhs ap output : Word)
    (pc : s.core.pc = 0) (running : s.halted = false) (hl : live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 output).toNat)
    (execution : Run ctx (program count rhs ap output) s final) :
    decode (read64 final.core.global (address (setup ctx s count).core 12 output).toNat) =
      decode (read64 s.core.global (address (setup ctx s count).core 12 rhs).toNat) -
      decode (read64 s.core.global (address (setup ctx s count).core 12 ap).toNat) ∧
    final.halted = true :=
  correct ctx s final count rhs ap output running hl hr ha ho
    (run_exec execution [] _ rfl pc)

/-- No resource limit is used as a substitute for a ret instruction. -/
theorem fetched_exists (ctx : Context) (s : State) (count : BitVec 32) (rhs ap output : Word)
    (pc : s.core.pc = 0) (running : s.halted = false) (hl : live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 output).toNat) :
    ∃ final, Run ctx (program count rhs ap output) s final := by
  obtain ⟨final,h⟩ := execution_exists ctx s count rhs ap output running hl hr ha ho
  exact ⟨final,exec_fetched h [] pc⟩

/-- Every completed fetched run preserves all bytes outside its one output
word, and never changes shared memory. -/
theorem fetched_frame (ctx : Context) (s final : State) (count : BitVec 32) (rhs ap output : Word)
    (pc : s.core.pc = 0) (running : s.halted = false) (hl : live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address (setup ctx s count).core 12 output).toNat)
    (execution : Run ctx (program count rhs ap output) s final) :
    (∀ p, p < (address (setup ctx s count).core 12 output).toNat ∨
      (address (setup ctx s count).core 12 output).toNat+8 ≤ p → final.core.global p = s.core.global p) ∧
    final.core.shared = s.core.shared := by
  have he : Exec ctx (program count rhs ap output) s final := run_exec execution [] _ rfl pc
  have hb : Exec ctx ((PTX.Residual.code rhs ap output).map Instr.data ++ [.ret]) (setup ctx s count) final :=
    (prologue_live hl running).mp (by simpa only [program,List.append_assoc] using he)
  obtain ⟨middle,hbody,hret⟩ := exec_block hb
  have runMiddle : ({setup ctx s count with core := middle} : State).halted = false := setup_live hl running
  have hend := (exec_halting_iff (i := .ret) (by simp) runMiddle rfl).mp hret
  subst final
  have h := PTX.Residual.correct _ _ rhs ap output
    (by simpa using hr) (by simpa using ha) (by simpa using ho) hbody
  simpa [simple,halt,advance,PTX.advance] using h.2

/-- Padding lanes have completed fetched executions without allocation premises. -/
theorem fetched_inactive (hn : ¬ live ctx count) (pc : s.core.pc = 0) (running : s.halted = false) :
    Run ctx (program count rhs ap output) s (setup ctx s count) ∧
    ∀ final, Run ctx (program count rhs ap output) s final →
      final.core.global = s.core.global ∧ final.core.shared = s.core.shared := by
  have he : Exec ctx (program count rhs ap output) s (setup ctx s count) := by
    apply (prologue_inactive hn running).mpr
    rfl
  exact ⟨exec_fetched he [] pc, fun final h => inactive (run_exec h [] _ rfl pc) hn running⟩

end PtxTorchLean.Poisson.PTX.Kernel.Residual
