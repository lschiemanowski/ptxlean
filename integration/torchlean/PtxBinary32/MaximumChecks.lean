import PtxBinary32.MaximumExecution

/-! Kernel-checked examples for selection and the actual fetched program.
These evaluate the software witness; they do not execute a GPU. -/
namespace Ptx.Scalar.Parallel.Maximum.Checks

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def seed : Scalar.State := ⟨73,fun _=>0xdeadbeef,fun _=>0x1234,fun _=>true,[0xffffffff]⟩

/-- One full instruction sweep per lane; each barrier sweep includes every
thread's actual arrival before the next instruction sweep begins. -/
def schedule (d : Nat) : List (Fin (width d)) :=
  (List.replicate (program d).length (List.finRange (width d))).flatten

def execute (d : Nat) (inputs : List Word) :=
  Reference.run (config d) (program d)
    (initial d (inputs++[0xdeadbeef]) (List.replicate (sharedWords d) 0x12345678) (fun _=>seed))
    (schedule d)

/-- Zero reduction levels still fetch publication, its barrier, output and exit. -/
theorem singleton :
    (execute 0 [0xbf800000]).1.global=[0xbf800000,0xbf800000] ∧
    ((execute 0 [0xbf800000]).1.lanes 0).halted=true := by decide

/-- Negative scores must not acquire a spurious zero from scratch storage. -/
theorem negative_tree :
    nodeValue [0xc0800000,0xc0000000,0xc1000000,0xbf800000] 2 0=0xbf800000 := by decide

/-- Both signs of zero participate, with positive zero selected at the root. -/
theorem signed_zero_tree :
    nodeValue [0x80000000,0,0x80000001,0xbf800000] 2 0=0 := by decide

/-- Eight scores exercise all three tree levels and normal/subnormal signs. -/
theorem eight_tree :
    nodeValue [0xbf800000,1,0x80000001,0x40400000,0x40000000,0xc0000000,0,0x80000000] 3 0=0x40400000 := by decide

/-- Concrete four-thread execution agrees with the tree, preserves all inputs,
and completes despite nonzero, arbitrary register and scratch seeds. -/
theorem negative_execution :
    (execute 2 [0xc0800000,0xc0000000,0xc1000000,0xbf800000]).1.global=
      [0xc0800000,0xc0000000,0xc1000000,0xbf800000,0xbf800000] ∧
    (∀t,((execute 2 [0xc0800000,0xc0000000,0xc1000000,0xbf800000]).1.lanes t).halted=true) ∧
    (execute 2 [0xc0800000,0xc0000000,0xc1000000,0xbf800000]).1.barrier.generation=3 := by decide

/-- The same fetched program completes all three levels for eight threads. -/
theorem eight_execution :
    (execute 3 [0xbf800000,1,0x80000001,0x40400000,0x40000000,0xc0000000,0,0x80000000]).1.global=
      [0xbf800000,1,0x80000001,0x40400000,0x40000000,0xc0000000,0,0x80000000,0x40400000] ∧
    (∀t,((execute 3 [0xbf800000,1,0x80000001,0x40400000,0x40000000,0xc0000000,0,0x80000000]).1.lanes t).halted=true) ∧
    (execute 3 [0xbf800000,1,0x80000001,0x40400000,0x40000000,0xc0000000,0,0x80000000]).1.barrier.generation=4 := by decide

end Ptx.Scalar.Parallel.Maximum.Checks
