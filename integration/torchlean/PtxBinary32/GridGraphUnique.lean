import PtxBinary32.GridGraphOrigins

/-! Initial cells and actual instruction positions have unique graph identities. -/
namespace Ptx.Scalar.Parallel.Grid.Memory
open Ptx.TraceMemory (Access Initial Projected Location identity)

private theorem cells_unique (words : List Word) (slot : Fin k) :
    ((words.mapIdx (fun i value => (⟨⟨slot,i⟩,value⟩ : Initial k))).map (fun i => i.location.code)).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map]
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj before eq
  simp only [List.getElem_mapIdx] at eq
  have same := congrArg Location.word (Location.code_injective eq)
  dsimp at same
  omega

theorem initials_unique (s : Grid.State groups n) : ((initials s).map (fun i => i.location.code)).Nodup := by
  simp only [initials,List.map_append,List.map_flatMap]
  rw [List.nodup_append]
  refine ⟨cells_unique _ _,?_,?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun g _ => cells_unique _ _,?_⟩
    apply List.Pairwise.imp_of_mem (p := (List.nodup_finRange groups))
    intro g h _ _ different
    apply List.disjoint_left.mpr
    intro code left right
    obtain ⟨a,ha,ea⟩ := List.mem_map.mp left
    obtain ⟨b,hb,eb⟩ := List.mem_map.mp right
    obtain ⟨i,hi,rfl⟩ := List.mem_mapIdx.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hb
    have same := congrArg (fun l : Location (groups+1) => l.storage.val) (Location.code_injective (ea.trans eb.symm))
    exact different (Fin.ext (by simpa using same))
  · intro code left other right equal
    subst other
    obtain ⟨a,ha,ea⟩ := List.mem_map.mp left
    obtain ⟨i,hi,rfl⟩ := List.mem_mapIdx.mp ha
    obtain ⟨g,_,inside⟩ := List.mem_flatMap.mp right
    obtain ⟨b,hb,eb⟩ := List.mem_map.mp inside
    obtain ⟨j,hj,rfl⟩ := List.mem_mapIdx.mp hb
    have same := congrArg (fun l : Location (groups+1) => l.storage.val) (Location.code_injective (ea.trans eb.symm))
    simp at same

theorem labels_unique (program : List Instr) (s : Grid.State groups n) (events : List (Grid.Event groups n)) :
    ((labels program s events).map identity).Nodup := by
  simp only [labels,List.map_append,List.map_map]
  rw [List.nodup_append]
  refine ⟨?_,?_,?_⟩
  · have h := (initials_unique s).map (f := fun p : Nat => ((none : Option Nat),p)) (by intro a b eq; exact (Prod.mk.inj eq).2)
    simpa [identity,Initial.occurrence,List.map_map,Function.comp_def] using h
  · apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    apply (Ptx.TraceMemory.project_ordered (access program) events).imp
    intro a b before eq
    have same := congrArg Prod.snd eq
    dsimp [identity,label,Function.comp_def] at same
    omega
  · intro id left other right equal
    subst other
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp left
    obtain ⟨p,hp,same⟩ := List.mem_map.mp right
    have emitted := ((Ptx.TraceMemory.project_member_iff _ _ _).mp hp).2
    obtain ⟨g,t,space,occ,effect,origin,_⟩ := access_origin program p.origin p.access emitted
    have impossible := congrArg Prod.fst (eq.trans same.symm)
    simp [Function.comp_def,identity,Initial.occurrence,label,origin,owner] at impossible

end Ptx.Scalar.Parallel.Grid.Memory
