import Boc.Scheduler

/-!
# Cown-acquisition deadlock freedom

Only acquisition waits are represented here.  Earlier-pending conflicts are
ordering constraints, not wait-for edges: an earlier pending behavior holds
no cown.
-/

namespace Boc

universe uC uI

variable {Cown : Type uC} {Id : Type uI}

/-!
Because acquisition is all-or-nothing, an acquisition edge starts at a pending
behavior and ends at an active holder.  There is no edge out of an active
behavior because the scheduler has no synchronous reacquisition rule.
-/

def waits_for (claims : Id → Set Cown)
    (scheduler : Scheduler Id)
    (waiter holder : Id) : Prop :=
  waiter ∈ scheduler.pending ∧
  holder ∈ scheduler.active ∧
  conflicts claims waiter holder

private theorem wait_path_source_pending
    {claims : Id → Set Cown} {scheduler : Scheduler Id} {x y : Id}
    (path : Relation.TransGen (waits_for claims scheduler) x y) :
    x ∈ scheduler.pending := by
  induction path with
  | single edge =>
      exact edge.1
  | tail path_prefix edge ih =>
      exact ih

private theorem wait_path_target_active
    {claims : Id → Set Cown} {scheduler : Scheduler Id} {x y : Id}
    (path : Relation.TransGen (waits_for claims scheduler) x y) :
    y ∈ scheduler.active := by
  induction path with
  | single edge =>
      exact edge.2.1
  | tail path_prefix edge ih =>
      exact edge.2.1

def has_acquisition_cycle
    (claims : Id → Set Cown) (scheduler : Scheduler Id) : Prop :=
  ∃ b, Relation.TransGen (waits_for claims scheduler) b b

theorem no_acquisition_cycle
    {claims : Id → Set Cown} {scheduler : Scheduler Id}
    (h_well_formed : well_formed scheduler) :
    ¬ has_acquisition_cycle claims scheduler := by
  intro cycle
  rcases cycle with ⟨b, path⟩
  exact h_well_formed.2
    (wait_path_source_pending path)
    (wait_path_target_active path)

theorem reachable_no_acquisition_cycle
    {claims : Id → Set Cown} {initial scheduler : Scheduler Id}
    (initial_well_formed : well_formed initial)
    (reachable : scheduler_reachable claims initial scheduler) :
    ¬ has_acquisition_cycle claims scheduler := by
  exact no_acquisition_cycle
    (reachable_well_formed initial_well_formed reachable)

end Boc
