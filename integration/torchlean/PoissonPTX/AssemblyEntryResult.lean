import PoissonPTX.AssemblyEntry

namespace PtxTorchLean.Poisson.PTX.Assembly

def entryValue (ctx : Kernel.Context) (count : BitVec 32) (offsets entries element : Word)
    (mask : Bool) (boundary : Word) (s : Flow.State) : Float :=
  let initial := (ready ctx count offsets s).core
  if mask=true ∧ maskFlag initial boundary≠0 then 0 else
    (List.range' (cursor initial) (limit initial-cursor initial)).foldl
      (fun acc k => acc+contribution initial entries element k) 0

theorem ready_zero : decode ((ready ctx count offsets s).core.regs 8)=(0 : Float) := by
  change decode (0 : Word)=(0 : Float)
  decide +kernel

/-- The entire active entry writes exactly one word. Its value is the ordered
assembly sum, or zero when the actual boundary flag requests masking. The
statement includes the final byte memory, so bytes outside that word are framed. -/
theorem entry_written
    (run : Flow.Runs ctx (entryCode count offsets entries element mask boundary output) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (live : Kernel.Residual.live ctx count) (prepareValid : PrepareValid (setup ctx count s).core offsets)
    (layout : Layout (ready ctx count offsets s).core entries element)
    (ordered : cursor (ready ctx count offsets s).core≤limit (ready ctx count offsets s).core)
    (maskValid : mask=true → Valid32 (ready ctx count offsets s).core.globalStart
      (ready ctx count offsets s).core.globalBytes (maskAddress (ready ctx count offsets s).core boundary).toNat)
    (outputValid : Valid64 (ready ctx count offsets s).core.globalStart (ready ctx count offsets s).core.globalBytes
      (address (ready ctx count offsets s).core 12 output).toNat) :
    ∃ word, t.core.global=write64 s.core.global (address (ready ctx count offsets s).core 12 output).toNat word ∧
      decode word=entryValue ctx count offsets entries element mask boundary s := by
  obtain ⟨steps,counted⟩ := Flow.counted run
  obtain ⟨remaining,loopEnd,trace,exit,alive,rest⟩ := entry_loop counted pc running done live prepareValid
  have calculation := window_correct trace (stable_refl _) ordered (valid_of_layout layout)
  have frame := calculation.2
  have node := window_node trace
  have outputAddress : address loopEnd.core 12 output=address (ready ctx count offsets s).core 12 output := by
    simp only [address,wide,frame.2.2.2.2.2.2.1,node]
  have boundaryAddress : maskAddress loopEnd.core boundary=maskAddress (ready ctx count offsets s).core boundary := by
    simp only [maskAddress,frame.2.2.2.2.2.2.1,node]
  have boundaryFlag : maskFlag loopEnd.core boundary=maskFlag (ready ctx count offsets s).core boundary := by
    simp only [maskFlag,frame.1,boundaryAddress]
  have final := entry_tail rest exit alive done
    (fun enabled => by simpa only [frame.2.2.1,frame.2.2.2.1,boundaryAddress] using maskValid enabled)
    (by simpa only [frame.2.2.1,frame.2.2.2.1,outputAddress] using outputValid)
  refine ⟨finalWord mask loopEnd.core boundary,?_,?_⟩
  · rw [final,tail_memory,outputAddress,frame.1]
    rfl
  · have value := calculation.1
    rw [ready_zero] at value
    cases mask with
    | false => simpa [finalWord,entryValue] using value
    | true =>
      by_cases isBoundary : maskFlag (ready ctx count offsets s).core boundary=0
      · simpa [finalWord,maskedWord,boundaryFlag,entryValue,isBoundary] using value
      · have zero : decode (0 : Word)=(0 : Float) := by decide +kernel
        simp only [finalWord, Bool.true_eq, ↓reduceIte, maskedWord, boundaryFlag, entryValue, true_and]
        split <;> simp_all

end PtxTorchLean.Poisson.PTX.Assembly
