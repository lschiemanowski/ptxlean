import PtxBinary32.GridGraph

/-! Each graph write is recovered from the actual tagged instruction trace or
an explicit initial cell. Initial global cells are shared, never per-group copies. -/
namespace Ptx.Scalar.Parallel.Grid.Memory
open Ptx.TraceMemory (Access Initial Projected Location AccessKind)

theorem access_origin (program : List Instr) (event : Grid.Event groups n) (a : Access (groups+1))
    (emitted : access program event=some a) :
    ∃ g t space occ effect, event=(g,.scalar t (some space) occ) ∧
      program[occ.pc]?=some (.memory space occ.instruction) ∧ occ.executed=true ∧
      occ.memory=some effect ∧ Parallel.Memory.Prior.memoryKind occ.instruction.op=some effect.kind ∧
      a=ofEffect g space effect := by
  obtain ⟨g,event⟩ := event
  cases event with
  | scalar t space occ =>
    cases space with
    | none => simp [access] at emitted
    | some space =>
      cases hm : occ.memory with
      | none => simp [access,hm] at emitted
      | some effect =>
        simp only [access,hm] at emitted
        split at emitted
        next h => exact ⟨g,t,space,occ,effect,rfl,h.1,h.2.1,hm,h.2.2,(Option.some.inj emitted).symm⟩
        next h => contradiction
  | _ => simp [access] at emitted

theorem labels_origin (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n))
    (event : Ptx.Occurrence) (member : event ∈ labels program s events) :
    (∃ i ∈ initials s, event=i.occurrence) ∨
    (∃ p : Projected (groups+1) (Grid.Event groups n),
      events[p.position]?=some p.origin ∧ access program p.origin=some p.access ∧ event=label p) := by
  rcases List.mem_append.mp member with init | prog
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp init
    exact .inl ⟨i,hi,rfl⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp prog
    have info := (Ptx.TraceMemory.project_member_iff _ _ _).mp hp
    exact .inr ⟨p,info.1,info.2,rfl⟩

theorem program_write_origin (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n))
    (source co) (w : Fin (labels program s events).length)
    (write : (graph program s events source co).write w)
    (noninitial : ¬(graph program s events source co).initial w) :
    ∃ g t p space occ effect, events[p]?=some (g,.scalar t (some space) occ) ∧
      program[occ.pc]?=some (.memory space occ.instruction) ∧ occ.executed=true ∧
      occ.memory=some effect ∧ effect.kind=.store ∧
      (graph program s events source co).event w=⟨some (threadId g t),p,(ofEffect g space effect).effect⟩ := by
  have member : (graph program s events source co).event w ∈ labels program s events := List.getElem_mem w.isLt
  rcases labels_origin program s events _ member with ⟨i,hi,he⟩ | ⟨p,hp,ha,he⟩
  · exact False.elim (noninitial (by simp [Graph.initial,he,Initial.occurrence]))
  · obtain ⟨g,t,space,occ,effect,origin,fetch,executed,memory,kind,value⟩ := access_origin program p.origin p.access ha
    have store : effect.kind=.store := by
      cases hk : effect.kind
      · simp [Graph.write,he,label,Access.effect,value,ofEffect,hk,AccessKind.op] at write
      · rfl
    refine ⟨g,t,p.position,space,occ,effect,?_,fetch,executed,memory,store,?_⟩
    · simpa [origin] using hp
    · rw [he]; simp [label,origin,owner,value]

theorem initial_origin (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n))
    (event : Ptx.Occurrence) (member : event ∈ labels program s events) (init : event.effect.op=.init) :
    ∃ i ∈ initials s, event=i.occurrence := by
  rcases labels_origin program s events event member with hi | ⟨p,hp,ha,he⟩
  · exact hi
  · obtain ⟨g,t,space,occ,effect,origin,fetch,executed,memory,kind,value⟩ := access_origin program p.origin p.access ha
    cases hk : effect.kind <;> simp [he,label,value,ofEffect,hk,Access.effect,AccessKind.op] at init

theorem initial_global (s : Grid.State groups n) (entry : Initial (groups+1)) (i : Nat)
    (member : entry ∈ initials s) (locationEq : entry.location=⟨0,i⟩) :
    i<s.global.length ∧ entry.value=s.global[i]! := by
  simp only [initials,List.mem_append,List.mem_mapIdx,List.mem_flatMap] at member
  rcases member with ⟨j,hj,rfl⟩ | ⟨g,_,j,hj,rfl⟩
  · have same := congrArg Location.word locationEq
    dsimp at same
    subst i
    exact ⟨hj,by simp [List.getElem!_eq_getElem?_getD,hj]⟩
  · have impossible := congrArg (fun l : Location (groups+1) => l.storage.val) locationEq
    simp at impossible

end Ptx.Scalar.Parallel.Grid.Memory
