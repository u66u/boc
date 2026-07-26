import Boc.Scheduler
import Boc.Simulation
import Mathlib.Logic.Function.Basic

/-!
# Full machine

A configuration pairs a scheduler state with a heap and per-behavior local
state.  Every full transition projects to a scheduler kernel transition or,
for body-internal `execute` steps, stutters; that forward simulation is the
only bridge the safety proofs need.
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

/-- Full-machine events: the scheduler events plus body-internal `execute`
steps, which the scheduler abstraction cannot observe. -/
inductive Config.Event (Id : Type*)
  | spawn (parent : Option Id) (b : Id)
  | execute (b : Id)
  | start (b : Id)
  | finish (b : Id)

inductive Config.Step (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body) :
    Config.Event Id → Config Id Heap Body → Config Id Heap Body → Prop
  | start
      {heap : Heap} {before after : List Id} {active : Set Id}
      {body : Id → Body} {b : Id}
      (is_eligible : Eligible claims b before active) :
      Config.Step claims semantics (.start b)
        ⟨heap, before ++ (b :: after), active, body⟩
        ⟨heap, before ++ after, insert b active, body⟩
  | execute
      {heap heap' : Heap} {pending : List Id} {active : Set Id}
      {body : Id → Body} {b : Id} {body' : Body}
      (is_active : b ∈ active)
      (steps : semantics.step b heap (body b) heap' body') :
      Config.Step claims semantics (.execute b)
        ⟨heap, pending, active, body⟩
        ⟨heap', pending, active, Function.update body b body'⟩
  | spawn
      {heap heap' : Heap} {pending : List Id} {active : Set Id}
      {body : Id → Body} {b q : Id} {body' childBody : Body}
      (is_active : b ∈ active)
      (is_fresh : Fresh q pending active)
      (spawns : semantics.spawn b heap (body b) q heap' body' childBody) :
      Config.Step claims semantics (.spawn (some b) q)
        ⟨heap, pending, active, body⟩
        ⟨heap', pending ++ [q], active,
          Function.update (Function.update body b body') q childBody⟩
  | finish
      {heap : Heap} {pending : List Id} {active : Set Id}
      {body : Id → Body} {b : Id}
      (is_active : b ∈ active)
      (is_finished : semantics.finished b (body b)) :
      Config.Step claims semantics (.finish b)
        ⟨heap, pending, active, body⟩
        ⟨heap, pending, active \ {b}, body⟩

/-- Some full-machine step fires, whatever its event. -/
abbrev Config.StepAny (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body)
    (config config' : Config Id Heap Body) : Prop :=
  ∃ e, Config.Step claims semantics e config config'

abbrev Config.Reachable (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body) :=
  Relation.ReflTransGen (Config.StepAny claims semantics)

/-! ## The projection simulation -/

/-- Event abstraction to the scheduler kernel: body-internal `execute` steps
are invisible, all other events map structurally. -/
def Config.Event.project : Config.Event Id → Option (Scheduler.Event Id)
  | .spawn parent b => some (.spawn parent b)
  | .execute _ => none
  | .start b => some (.start b)
  | .finish b => some (.finish b)

theorem Config.Step.projects
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body} :
    Simulation (Config.Step claims semantics) (Scheduler.Step claims)
      Config.scheduler Config.Event.project fun _ => True := by
  intro e source target _ step
  cases step with
  | start is_eligible => exact Scheduler.Step.start is_eligible
  | execute is_active steps => rfl
  | spawn is_active is_fresh spawns => exact Scheduler.Step.spawn is_fresh
  | finish is_active is_finished => exact Scheduler.Step.finish is_active

theorem Config.reachable_projects
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (reachable : Config.Reachable claims semantics initial config) :
    Scheduler.Reachable claims initial.scheduler config.scheduler :=
  Config.Step.projects.liftOption (fun _ _ _ _ _ => trivial) trivial reachable

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
