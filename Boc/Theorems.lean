import Boc.Deadlock
import Boc.Heap
import Boc.Semantics

namespace Boc

variable {Cown Id Slot : Type*} {Heap Body : Type*}
variable [DecidableEq Id]

/-- The body language may define access differently at every full
configuration.  This is the abstract form of the heap-isolation
obligation. -/
def ExecutionHeapIsolated
    (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body)
    (initial : Config Id Heap Body)
    (may_access :
      Config Id Heap Body →
      Id → Location Cown Slot → AccessMode → Prop) : Prop :=
  ∀ ⦃config⦄,
    Config.Reachable claims semantics initial config →
    HeapIsolated claims (may_access config)

theorem Config.reachable_race_free
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    {may_access :
      Config Id Heap Body →
      Id → Location Cown Slot → AccessMode → Prop}
    (initial_safe : Safe claims initial.active)
    (reachable : Config.Reachable claims semantics initial config)
    (h_isolated : ExecutionHeapIsolated claims semantics initial may_access) :
    ¬ HasRace config.active (may_access config) :=
  safe_implies_race_free
    (Config.reachable_safe initial_safe reachable)
    (h_isolated reachable)

theorem Config.reachable_no_acquisition_cycle
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_wf : initial.scheduler.WellFormed)
    (reachable : Config.Reachable claims semantics initial config) :
    ¬ HasAcquisitionCycle claims config.scheduler :=
  no_acquisition_cycle (Config.reachable_wellFormed initial_wf reachable)

end Boc
