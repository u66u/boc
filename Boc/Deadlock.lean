import Boc.Scheduler

/-!
# Cown-acquisition deadlock freedom

Only acquisition waits are represented here.  Earlier-pending conflicts are
ordering constraints, not wait-for edges: an earlier pending behavior holds
no cown.

The main theorem is deliberately near-immediate.  Because acquisition is
all-or-nothing, every wait-for edge runs from a pending behavior to an
active holder — there is no edge out of an active behavior, since the
scheduler has no synchronous reacquisition rule.  A cycle would therefore
need a behavior that is both pending and active, which well-formedness
forbids.  That triviality is the point: the model leaves no state in which a
behavior holds some cowns while waiting for more.
-/

namespace Boc

variable {Cown Id : Type*}

def WaitsFor (claims : Id → Set Cown)
    (scheduler : Scheduler Id)
    (waiter holder : Id) : Prop :=
  waiter ∈ scheduler.pending ∧
  holder ∈ scheduler.active ∧
  Conflicts claims waiter holder

private theorem wait_path_source_pending
    {claims : Id → Set Cown} {scheduler : Scheduler Id} {x y : Id}
    (path : Relation.TransGen (WaitsFor claims scheduler) x y) :
    x ∈ scheduler.pending := by
  induction path with
  | single edge => exact edge.1
  | tail _ _ ih => exact ih

private theorem wait_path_target_active
    {claims : Id → Set Cown} {scheduler : Scheduler Id} {x y : Id}
    (path : Relation.TransGen (WaitsFor claims scheduler) x y) :
    y ∈ scheduler.active := by
  induction path with
  | single edge => exact edge.2.1
  | tail _ edge _ => exact edge.2.1

def HasAcquisitionCycle
    (claims : Id → Set Cown) (scheduler : Scheduler Id) : Prop :=
  ∃ b, Relation.TransGen (WaitsFor claims scheduler) b b

theorem no_acquisition_cycle
    {claims : Id → Set Cown} {scheduler : Scheduler Id}
    (h_wf : scheduler.WellFormed) :
    ¬ HasAcquisitionCycle claims scheduler :=
  fun ⟨_, path⟩ =>
    h_wf.2 _ (wait_path_source_pending path) (wait_path_target_active path)

theorem Scheduler.reachable_no_acquisition_cycle
    {claims : Id → Set Cown} {initial scheduler : Scheduler Id}
    (initial_wf : initial.WellFormed)
    (reachable : Scheduler.Reachable claims initial scheduler) :
    ¬ HasAcquisitionCycle claims scheduler :=
  no_acquisition_cycle (Scheduler.reachable_wellFormed initial_wf reachable)

end Boc
