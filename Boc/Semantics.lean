import Boc.Scheduler
import Mathlib.Logic.Function.Basic

/-!
# Full machine

A configuration pairs a scheduler state with a heap and per-behavior local
state.  Every full transition projects to a scheduler kernel transition;
that projection is the only bridge the safety proofs need.
-/

namespace Boc

variable {Cown Id : Type*} {Heap Body : Type*}
variable [DecidableEq Id]

structure Config (Id : Type*) (Heap : Type*) (Body : Type*) where
  heap : Heap
  pending : List Id
  active : Set Id
  body : Id → Body

def Config.scheduler (config : Config Id Heap Body) : Scheduler Id :=
  ⟨config.pending, config.active⟩

/-- What the body language must supply.  `step` changes the heap and one
active body's local state, `spawn` additionally returns the fresh child's
initial state, and `finished` marks completed bodies.  The body language is
otherwise unconstrained. -/
structure BodySemantics (Id : Type*) (Heap : Type*) (Body : Type*) where
  step : (b : Id) → (heap : Heap) → (body : Body) →
    (heap' : Heap) → (body' : Body) → Prop
  spawn : (parent : Id) → (heap : Heap) → (body : Body) → (child : Id) →
    (heap' : Heap) → (body' : Body) → (childBody : Body) → Prop
  finished : (b : Id) → (body : Body) → Prop

inductive Config.Step (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body) :
    Config Id Heap Body → Config Id Heap Body → Prop
  | start
      {heap : Heap} {before after : List Id} {active : Set Id}
      {body : Id → Body} {b : Id}
      (is_eligible : Eligible claims b before active) :
      Config.Step claims semantics
        ⟨heap, before ++ (b :: after), active, body⟩
        ⟨heap, before ++ after, insert b active, body⟩
  | execute
      {heap heap' : Heap} {pending : List Id} {active : Set Id}
      {body : Id → Body} {b : Id} {body' : Body}
      (is_active : b ∈ active)
      (steps : semantics.step b heap (body b) heap' body') :
      Config.Step claims semantics
        ⟨heap, pending, active, body⟩
        ⟨heap', pending, active, Function.update body b body'⟩
  | spawn
      {heap heap' : Heap} {pending : List Id} {active : Set Id}
      {body : Id → Body} {b q : Id} {body' childBody : Body}
      (is_active : b ∈ active)
      (is_fresh : Fresh q pending active)
      (spawns : semantics.spawn b heap (body b) q heap' body' childBody) :
      Config.Step claims semantics
        ⟨heap, pending, active, body⟩
        ⟨heap', pending ++ [q], active,
          Function.update (Function.update body b body') q childBody⟩
  | finish
      {heap : Heap} {pending : List Id} {active : Set Id}
      {body : Id → Body} {b : Id}
      (is_active : b ∈ active)
      (is_finished : semantics.finished b (body b)) :
      Config.Step claims semantics
        ⟨heap, pending, active, body⟩
        ⟨heap, pending, active \ {b}, body⟩

abbrev Config.Reachable (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body) :=
  Relation.ReflTransGen (Config.Step claims semantics)

/-! ## The projection lemma -/

theorem Config.Step.projects
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {source target : Config Id Heap Body}
    (step : Config.Step claims semantics source target) :
    Scheduler.Step claims source.scheduler target.scheduler := by
  cases step with
  | start is_eligible => exact Scheduler.Step.start is_eligible
  | execute is_active steps => exact Scheduler.Step.internal
  | spawn is_active is_fresh spawns => exact Scheduler.Step.spawn is_fresh
  | finish is_active is_finished => exact Scheduler.Step.finish is_active

theorem Config.reachable_projects
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (reachable : Config.Reachable claims semantics initial config) :
    Scheduler.Reachable claims initial.scheduler config.scheduler :=
  reachable.lift Config.scheduler fun _ _ step => step.projects

theorem Config.reachable_safe
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_safe : Safe claims initial.active)
    (reachable : Config.Reachable claims semantics initial config) :
    Safe claims config.active :=
  Scheduler.reachable_safe initial_safe (Config.reachable_projects reachable)

theorem Config.reachable_wellFormed
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_wf : initial.scheduler.WellFormed)
    (reachable : Config.Reachable claims semantics initial config) :
    config.scheduler.WellFormed :=
  Scheduler.reachable_wellFormed initial_wf (Config.reachable_projects reachable)

end Boc
