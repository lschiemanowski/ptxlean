import Ptx.SharedReductionControl
import Ptx.TraceMemory

/-! One combined graph projected from the actual reduction machine trace.
Positions are complete global trace indices, including nonmemory and other-thread
events; their restriction to one thread is its dynamic order. -/
namespace Ptx.Scalar.SharedReduction.Machine.Memory

open Ptx.TraceMemory

/-- Slot zero is global, slot one CTA-shared. Numeric offsets never select space. -/
def slot : Space → Fin 2
  | .global => 0
  | .shared => 1

def location (space : Space) (address : Scalar.Address) : Location 2 :=
  ⟨slot space, address.toNat / 4⟩

def catalogue (device grid cluster cta globalAllocation sharedAllocation : Nat) : Catalogue 2 where
  key := fun i => if i.val = 0 then .global globalAllocation
    else .shared device grid cluster cta sharedAllocation
  distinct := by
    intro a b same
    have ha := a.isLt
    have hb := b.isLt
    by_cases az : a.val = 0 <;> by_cases bz : b.val = 0
    · exact Fin.ext (az.trans bz.symm)
    · simp [az,bz] at same
    · simp [az,bz] at same
    · apply Fin.ext; omega

theorem spaces_distinct (a b : Scalar.Address) :
    (location .global a).code ≠ (location .shared b).code := by
  intro h
  have h := congrArg (fun l : Location 2 => l.storage.val) (Location.code_injective h)
  simp [location,slot] at h

/-- Alignment is a separately proved input to exact byte-address recovery. -/
theorem byte_recover (space : Space) (address : Scalar.Address)
    (aligned : address.toNat % 4 = 0) : 4 * (location space address).word = address.toNat := by
  have h := Nat.mod_add_div address.toNat 4
  simp only [aligned, Nat.zero_add] at h
  exact h

def kindMatches (op : Scalar.Op) (kind : MemoryKind) : Bool :=
  match op, kind with
  | .load _ _, .load | .store _ _, .store => true
  | _, _ => false

def ofEffect (space : Space) (effect : MemoryEffect) : Access 2 :=
  ⟨location space effect.address,
    match effect.kind with | .load => .load .relaxed | .store => .store .relaxed,
    effect.value⟩

/-- The adapter admits only an executed effect from the actual typed memory
instruction fetched at that block/PC, with matching load/store direction. -/
def access (thread : Nat) : Event n → Option (Access 2)
  | .scalar t block (some space) occ =>
    match occ.memory with
    | none => none
    | some effect =>
      if t.val = thread ∧ (program n block)[occ.pc]? = some (.memory space occ.instruction) ∧
          occ.executed = true ∧ kindMatches occ.instruction.op effect.kind = true
      then some (ofEffect space effect) else none
  | _ => none

theorem access_origin (thread : Nat) (event : Event n) (a : Access 2)
    (emitted : access thread event = some a) :
    ∃ t block space occ effect,
      event = .scalar t block (some space) occ ∧ t.val = thread ∧
      (program n block)[occ.pc]? = some (.memory space occ.instruction) ∧
      occ.executed = true ∧ occ.memory = some effect ∧
      kindMatches occ.instruction.op effect.kind = true ∧ a = ofEffect space effect := by
  cases event with
  | scalar t block space occ =>
    cases space with
    | none => simp [access] at emitted
    | some space =>
      cases hm : occ.memory with
      | none => simp [access,hm] at emitted
      | some effect =>
        simp only [access,hm] at emitted
        split at emitted
        next h => exact ⟨t,block,space,occ,effect,rfl,h.1,h.2.1,h.2.2.1,hm,h.2.2.2,
          (Option.some.inj emitted).symm⟩
        next h => contradiction
  | branch => simp [access] at emitted
  | barrier => simp [access] at emitted
  | exit => simp [access] at emitted

theorem access_complete (t : Fin n) (block : Machine.Block) (space : Space)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (fetch : (program n block)[occ.pc]? = some (.memory space occ.instruction))
    (executed : occ.executed = true) (memory : occ.memory = some effect)
    (kind : kindMatches occ.instruction.op effect.kind = true) :
    access t.val (.scalar t block (some space) occ) = some (ofEffect space effect) := by
  simp [access,fetch,executed,memory,kind]

/-- A graph access retains the original byte effect; no divided-address guess is
used to recover its fetched instruction or its value. -/
theorem access_fields (thread : Nat) (event : Event n) (a : Access 2)
    (emitted : access thread event = some a) :
    ∃ t block space occ effect,
      event = .scalar t block (some space) occ ∧ occ.memory = some effect ∧
      a.location = location space effect.address ∧ a.value = effect.value ∧
      a.kind = (match effect.kind with | .load => .load .relaxed | .store => .store .relaxed) := by
  obtain ⟨t,block,space,occ,effect,he,_,_,_,hm,_,rfl⟩ := access_origin thread event a emitted
  exact ⟨t,block,space,occ,effect,he,hm,rfl,rfl,rfl⟩

def projection (thread : Nat) (trace : List (Event n)) : List (Projected 2 (Event n)) :=
  project (access thread) trace

theorem projection_origin (thread : Nat) (trace : List (Event n))
    (p : Projected 2 (Event n)) (member : p ∈ projection thread trace) :
    trace[p.position]? = some p.origin ∧ access thread p.origin = some p.access :=
  (project_member_iff _ _ _).mp member

theorem projection_complete (thread : Nat) (trace : List (Event n))
    (position : Nat) (event : Event n) (a : Access 2)
    (atIndex : trace[position]? = some event) (emitted : access thread event = some a) :
    (⟨position,event,a⟩ : Projected 2 (Event n)) ∈ projection thread trace :=
  TraceMemory.project_complete _ _ atIndex emitted

theorem projection_unique (thread : Nat) (trace : List (Event n))
    (p q : Projected 2 (Event n)) (hp : p ∈ projection thread trace)
    (hq : q ∈ projection thread trace) (same : p.position = q.position) : p = q :=
  project_unique _ _ hp hq same

theorem projection_ordered (thread : Nat) (trace : List (Event n)) :
    (projection thread trace).Pairwise (fun p q => p.position < q.position) :=
  project_ordered _ _

/-- Initial words are supplied, including arbitrary initial scratch and output. -/
def initial (global shared : List Word) : List (Initial 2) :=
  global.mapIdx (fun i value => ⟨⟨0,i⟩,value⟩) ++
  shared.mapIdx (fun i value => ⟨⟨1,i⟩,value⟩)

def labels (global shared : List Word) (trace : List (Event n)) : List Ptx.Occurrence :=
  TraceMemory.events (initial global shared) (List.range n) (fun _ => trace) access

def graph (global shared : List Word) (trace : List (Event n))
    (source : Fin (labels global shared trace).length → Fin (labels global shared trace).length)
    (co : Fin (labels global shared trace).length → Fin (labels global shared trace).length → Bool) :=
  TraceMemory.graph (labels global shared trace) source co

theorem labels_origin (global shared : List Word) (trace : List (Event n))
    (event : Ptx.Occurrence) (member : event ∈ labels global shared trace) :
    (∃ i ∈ initial global shared, i.occurrence = event) ∨
    (∃ t, t < n ∧ ∃ p : Projected 2 (Event n),
      trace[p.position]? = some p.origin ∧ access t p.origin = some p.access ∧
      p.occurrence t = event) := by
  simpa [labels,List.mem_range] using
    (events_member_iff (initial global shared) (List.range n) (fun _ => trace) access event).mp member

theorem initial_unique (global shared : List Word) :
    ((initial global shared).map Initial.location).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map,initial,List.pairwise_append]
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    simp only [List.getElem_mapIdx]
    intro same
    have h := congrArg (fun l : Location 2 => l.word) same
    simp at h
    omega
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    simp only [List.getElem_mapIdx]
    intro same
    have h := congrArg (fun l : Location 2 => l.word) same
    simp at h
    omega
  · intro x hx y hy same
    obtain ⟨i,hi,hx⟩ := List.mem_mapIdx.mp hx
    obtain ⟨j,hj,hy⟩ := List.mem_mapIdx.mp hy
    subst x; subst y
    have h := congrArg (fun l : Location 2 => l.storage.val) same
    simp at h

theorem labels_unique (global shared : List Word) (trace : List (Event n)) :
    ((labels global shared trace).map identity).Nodup :=
  events_unique _ _ _ _ (initial_unique global shared) List.nodup_range

/-- Initial global locations have exactly their supplied word, with a real bound. -/
theorem initial_global (global shared : List Word) (i : Initial 2) (word : Nat)
    (member : i ∈ initial global shared) (atWord : i.location = ⟨0,word⟩) :
    word < global.length ∧ i.value = global[word]! := by
  rcases List.mem_append.mp member with hg | hs
  · obtain ⟨index,bound,rfl⟩ := List.mem_mapIdx.mp hg
    have indexEq : index = word := congrArg Location.word atWord
    subst index
    exact ⟨bound, by simp [bound]⟩
  · obtain ⟨index,bound,rfl⟩ := List.mem_mapIdx.mp hs
    have impossible := congrArg (fun l : Location 2 => l.storage.val) atWord
    simp at impossible

theorem initial_shared (global shared : List Word) (i : Initial 2) (word : Nat)
    (member : i ∈ initial global shared) (atWord : i.location = ⟨1,word⟩) :
    word < shared.length ∧ i.value = shared[word]! := by
  rcases List.mem_append.mp member with hg | hs
  · obtain ⟨index,bound,rfl⟩ := List.mem_mapIdx.mp hg
    have impossible := congrArg (fun l : Location 2 => l.storage.val) atWord
    simp at impossible
  · obtain ⟨index,bound,rfl⟩ := List.mem_mapIdx.mp hs
    have indexEq : index = word := congrArg Location.word atWord
    subst index
    exact ⟨bound, by simp [bound]⟩

/-- A program write in the graph comes from a store effect at its exact trace
position; source/coherence choices cannot invent another write. -/
theorem program_write_origin (global shared : List Word) (trace : List (Event n))
    (source co) (w : Fin (labels global shared trace).length)
    (write : (graph global shared trace source co).write w)
    (noninitial : ¬(graph global shared trace source co).initial w) :
    ∃ thread position block space occ effect,
      trace[position]? = some (.scalar thread block (some space) occ) ∧
      (program n block)[occ.pc]? = some (.memory space occ.instruction) ∧
      occ.executed = true ∧ occ.memory = some effect ∧ effect.kind = .store ∧
      (graph global shared trace source co).event w =
        ⟨some thread.val,position,(ofEffect space effect).effect⟩ := by
  have mem : (graph global shared trace source co).event w ∈ labels global shared trace :=
    List.getElem_mem w.isLt
  rcases labels_origin global shared trace _ mem with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
  · exact False.elim (noninitial (by simp [Graph.initial,← he,Initial.occurrence]))
  · obtain ⟨thread,block,space,occ,effect,origin,threadEq,fetch,executed,memory,kind,value⟩ :=
      access_origin t p.origin p.access ha
    have store : effect.kind = .store := by
      cases hk : effect.kind
      · simp [Graph.write,← he,Projected.occurrence,Access.effect,value,ofEffect,hk,AccessKind.op] at write
      · rfl
    refine ⟨thread,p.position,block,space,occ,effect,?_,fetch,executed,memory,store,?_⟩
    · simpa [origin] using hp
    · rw [← he]
      simp [Projected.occurrence,value,threadEq]

/-- Source compatibility supplies a real initial word or a real projected store,
with the same graph address and value as the read. It does not assert freshness. -/
theorem source_origin (global shared : List Word) (trace : List (Event n))
    (source co) (r : Fin (labels global shared trace).length)
    (sources : (graph global shared trace source co).Sources)
    (read : (graph global shared trace source co).read r) :
    let g := graph global shared trace source co
    g.sameAddress (g.source r) r ∧
    (g.event (g.source r)).effect.value = (g.event r).effect.value ∧
    ((∃ i ∈ initial global shared, i.occurrence = g.event (g.source r)) ∨
      ∃ thread position block space occ effect,
        trace[position]? = some (.scalar thread block (some space) occ) ∧
        (program n block)[occ.pc]? = some (.memory space occ.instruction) ∧
        occ.executed = true ∧ occ.memory = some effect ∧ effect.kind = .store ∧
        g.event (g.source r) = ⟨some thread.val,position,(ofEffect space effect).effect⟩) := by
  obtain ⟨write,address,value⟩ := sources.compatible r read
  refine ⟨address,value,?_⟩
  by_cases init : (graph global shared trace source co).initial ((graph global shared trace source co).source r)
  · have member : (graph global shared trace source co).event ((graph global shared trace source co).source r)
        ∈ labels global shared trace := List.getElem_mem _
    rcases labels_origin global shared trace _ member with hi | ⟨t,ht,p,hp,ha,he⟩
    · exact Or.inl hi
    · have impossible : p.access.kind.op = .init := by
        simpa [Graph.initial,← he,Projected.occurrence,Access.effect] using init
      cases hk : p.access.kind <;> simp [AccessKind.op,hk] at impossible
  · exact Or.inr (program_write_origin global shared trace source co _ write init)

theorem kindMatches_iff (op : Scalar.Op) (kind : MemoryKind) :
    kindMatches op kind = true ↔ Control.memoryKind op = some kind := by
  cases op <;> cases kind <;> simp [kindMatches,Control.memoryKind]

/-- Every emitted actual memory effect, including arbitrary candidate reads,
passes the adapter. This needs no desired values or completed-run assumption. -/
theorem run_access_complete (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (thread : Fin n) (block : Machine.Block)
    (space : Option Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (member : .scalar thread block space occ ∈ (runWith cfg reads schedule s).trace)
    (memory : occ.memory = some effect) :
    ∃ actualSpace, space = some actualSpace ∧
      access thread.val (.scalar thread block space occ) = some (ofEffect actualSpace effect) := by
  obtain ⟨actualSpace,rfl,fetch,executed,kind⟩ :=
    Control.runWith_memory_origin cfg reads schedule s thread block space occ effect member memory
  exact ⟨actualSpace,rfl,access_complete thread block actualSpace occ effect fetch executed memory
    ((kindMatches_iff _ _).mpr kind)⟩

theorem run_projection_complete (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (position : Nat)
    (thread : Fin n) (block : Machine.Block) (space : Option Space)
    (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (atIndex : (runWith cfg reads schedule s).trace[position]? = some (.scalar thread block space occ))
    (memory : occ.memory = some effect) :
    ∃ actualSpace, space = some actualSpace ∧
      (⟨position,.scalar thread block space occ,ofEffect actualSpace effect⟩ : Projected 2 (Event n))
        ∈ projection thread.val (runWith cfg reads schedule s).trace := by
  obtain ⟨actualSpace,spaceEq,complete⟩ := run_access_complete cfg reads schedule s thread block space occ effect
    (List.mem_of_getElem? atIndex) memory
  exact ⟨actualSpace,spaceEq,projection_complete _ _ _ _ _ atIndex complete⟩

/-- No actual global store targets an input slot: its fetched address is the
separate output slot n, regardless of schedules, candidate values or registers. -/
theorem program_global_write_address (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (global shared : List Word)
    (source co) (w : Fin (labels global shared (runWith cfg reads schedule s).trace).length)
    (write : (graph global shared (runWith cfg reads schedule s).trace source co).write w)
    (noninitial : ¬(graph global shared (runWith cfg reads schedule s).trace source co).initial w)
    (word : Nat)
    (address : ((graph global shared (runWith cfg reads schedule s).trace source co).event w).effect.address =
      (⟨0,word⟩ : Location 2).code) : word = n := by
  obtain ⟨thread,position,block,space,occ,effect,atIndex,fetch,executed,memory,store,label⟩ :=
    program_write_origin global shared _ source co w write noninitial
  have locations : location space effect.address = (⟨0,word⟩ : Location 2) := by
    apply Location.code_injective
    simpa [label,ofEffect,Access.effect] using address
  cases space with
  | shared =>
    have impossible := congrArg (fun l : Location 2 => l.storage.val) locations
    simp [location,slot] at impossible
  | global =>
    have output := Control.runWith_global_store_address cfg reads schedule s thread block occ effect
      (List.mem_of_getElem? atIndex) memory store
    have wordEq := congrArg Location.word locations
    have fits : 4*n < 2^64 := by have := cfg.noWrap; omega
    simpa [location,output,bytePointer,Nat.mod_eq_of_lt fits] using wordEq.symm

/-- Every compatible read of a global input word comes from its actual initial
word. Neither source identity nor the input value is an assumption. -/
theorem global_input_read (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (global shared : List Word)
    (source co) (r : Fin (labels global shared (runWith cfg reads schedule s).trace).length)
    (sources : (graph global shared (runWith cfg reads schedule s).trace source co).Sources)
    (read : (graph global shared (runWith cfg reads schedule s).trace source co).read r)
    (word : Nat) (input : word < n)
    (address : ((graph global shared (runWith cfg reads schedule s).trace source co).event r).effect.address =
      (⟨0,word⟩ : Location 2).code) :
    let g := graph global shared (runWith cfg reads schedule s).trace source co
    g.initial (g.source r) ∧ word < global.length ∧ (g.event r).effect.value = global[word]! := by
  let g := graph global shared (runWith cfg reads schedule s).trace source co
  obtain ⟨write,same,value⟩ := sources.compatible r read
  have sourceAddress : (g.event (g.source r)).effect.address = (⟨0,word⟩ : Location 2).code :=
    same.trans address
  have init : g.initial (g.source r) := by
    by_cases yes : g.initial (g.source r)
    · exact yes
    have noninitial := yes
    have output := program_global_write_address cfg reads schedule s global shared source co
      (g.source r) write noninitial word sourceAddress
    omega
  refine ⟨init,?_⟩
  have member : g.event (g.source r) ∈ labels global shared (runWith cfg reads schedule s).trace :=
    List.getElem_mem _
  rcases labels_origin global shared _ _ member with ⟨i,hi,he⟩ | ⟨t,ht,p,hp,ha,he⟩
  · have locationEq : i.location = (⟨0,word⟩ : Location 2) := by
      apply Location.code_injective
      simpa [← he,Initial.occurrence] using sourceAddress
    obtain ⟨bound,initialValue⟩ := initial_global global shared i word hi locationEq
    refine ⟨bound,?_⟩
    rw [← value,← he]
    exact initialValue
  · have impossible : p.access.kind.op = .init := by
      simpa [Graph.initial,← he,Projected.occurrence,Access.effect] using init
    cases hk : p.access.kind <;> simp [AccessKind.op,hk] at impossible

/-- The execution-facing constructor fixes initialization to the actual incoming
arenas, as well as fixing every program label to the actual emitted trace. -/
def runLabels (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) : List Ptx.Occurrence :=
  labels s.global s.shared (runWith cfg reads schedule s).trace

def runGraph (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n)
    (source : Fin (runLabels cfg reads schedule s).length → Fin (runLabels cfg reads schedule s).length)
    (co : Fin (runLabels cfg reads schedule s).length → Fin (runLabels cfg reads schedule s).length → Bool) :=
  graph s.global s.shared (runWith cfg reads schedule s).trace source co

theorem run_global_input_read (cfg : Config n) (reads : Nat → Option Word)
    (schedule : List (Fin n)) (s : State n) (source co)
    (r : Fin (runLabels cfg reads schedule s).length)
    (sources : (runGraph cfg reads schedule s source co).Sources)
    (read : (runGraph cfg reads schedule s source co).read r)
    (word : Nat) (input : word < n)
    (address : ((runGraph cfg reads schedule s source co).event r).effect.address =
      (⟨0,word⟩ : Location 2).code) :
    let g := runGraph cfg reads schedule s source co
    g.initial (g.source r) ∧ word < s.global.length ∧ (g.event r).effect.value = s.global[word]! :=
  global_input_read cfg reads schedule s s.global s.shared source co r sources read word input address

end Ptx.Scalar.SharedReduction.Machine.Memory
