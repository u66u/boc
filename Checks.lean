import Boc
import Lean

/-!
# Quality gates: statement pinning + axiom audit

CI runs `lake env lean Checks.lean`.

Part 1 restates the trusted-surface theorems verbatim.  If a refactor drifts a
statement, this file breaks — changing it is how a statement change is made
deliberate and visible in review.

Part 2 asserts the axiom footprint of the trusted surface.  `sorry` anywhere in
the proof cone shows up as `sorryAx` and fails the gate.
-/

namespace Boc.Checks

open Boc

/-! ## Part 1: pinned statements -/

example {Cown Id : Type*} {claims : Id → Set Cown}
    {initial scheduler : Scheduler Id}
    (initial_safe : Safe claims initial.active)
    (reachable : Scheduler.Reachable claims initial scheduler) :
    Safe claims scheduler.active :=
  Scheduler.reachable_safe initial_safe reachable

example {Cown Id : Type*} {claims : Id → Set Cown} {scheduler : Scheduler Id}
    (h_wf : scheduler.WellFormed) :
    ¬ HasAcquisitionCycle claims scheduler :=
  no_acquisition_cycle h_wf

example {Cown Id Slot : Type*} {Heap Body : Type*} [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    {may_access :
      Config Id Heap Body → Id → Location Cown Slot → AccessMode → Prop}
    (initial_safe : Safe claims initial.active)
    (reachable : Config.Reachable claims semantics initial config)
    (h_isolated : ExecutionHeapIsolated claims semantics initial may_access) :
    ¬ HasRace config.active (may_access config) :=
  Config.reachable_race_free initial_safe reachable h_isolated

example {Cown Id : Type*} {Heap Body : Type*} [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_wf : initial.scheduler.WellFormed)
    (reachable : Config.Reachable claims semantics initial config) :
    ¬ HasAcquisitionCycle claims config.scheduler :=
  Config.reachable_no_acquisition_cycle initial_wf reachable

example {Cown Id : Type*} {Heap Body : Type*} [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {config : Config Id Heap Body}
    (h_progress : BodyProgress semantics config) :
    Terminal config ∨
      ∃ config', Config.Step claims semantics config config' :=
  nonstuck h_progress

/-! ## Part 2: axiom audit -/

open Lean in
#eval show CoreM Unit from do
  -- must be axiom-free
  for t in [``Boc.Scheduler.reachable_safe, ``Boc.Config.reachable_race_free,
      ``Boc.safe_implies_race_free] do
    let axs ← collectAxioms t
    unless axs.isEmpty do
      throwError "gate: {t} must be axiom-free, depends on {axs}"
  -- classical allowed, nothing else (sorryAx fails here)
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  for t in [``Boc.nonstuck, ``Boc.no_acquisition_cycle,
      ``Boc.Config.reachable_no_acquisition_cycle,
      ``Boc.Scheduler.reachable_wellFormed] do
    let axs ← collectAxioms t
    for a in axs do
      unless allowed.contains a do
        throwError "gate: {t} depends on disallowed axiom {a}"

end Boc.Checks
