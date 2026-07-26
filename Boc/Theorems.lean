import Boc.Deadlock
import Boc.Heap
import Boc.Semantics

/-!
connect full executions to the independent scheduler and memory proofs.
-/

namespace Boc

universe uC uI uS uH uB

variable {Cown : Type uC} {Id : Type uI} {Slot : Type uS}
variable {Heap : Type uH} {Body : Type uB}

/-!
The body language may define access differently at every full configuration.
This is the abstract form of the heap-isolation obligation.
-/

def execution_heap_isolated
    [DecidableEq Id]
    (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body)
    (initial : Config Id Heap Body)
    (may_access :
      Config Id Heap Body →
      Id → Location Cown Slot → access_mode → Prop) : Prop :=
  ∀ ⦃config⦄,
    global_reachable claims semantics initial config →
    heap_isolated claims (may_access config)

theorem global_reachable_race_free
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    {may_access :
      Config Id Heap Body →
      Id → Location Cown Slot → access_mode → Prop}
    (initial_safe : safe claims initial.active)
    (reachable : global_reachable claims semantics initial config)
    (h_isolated :
      execution_heap_isolated claims semantics initial may_access) :
    ¬ has_race config.active (may_access config) := by
  exact safe_implies_race_free
    (global_reachable_safe initial_safe reachable)
    (h_isolated reachable)

theorem global_reachable_no_acquisition_cycle
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_well_formed : well_formed initial.scheduler)
    (reachable : global_reachable claims semantics initial config) :
    ¬ has_acquisition_cycle claims config.scheduler := by
  exact no_acquisition_cycle
    (global_reachable_well_formed initial_well_formed reachable)

end Boc
