import Boc.Scheduler
import Mathlib.Logic.Function.Basic

namespace Boc

universe uC uI uH uB

variable {Cown : Type uC} {Id : Type uI}
variable {Heap : Type uH} {Body : Type uB}

structure Config
    (Id : Type uI) (Heap : Type uH) (Body : Type uB) where
  heap : Heap
  pending : List Id
  active : Set Id
  body : Id → Body

def Config.scheduler
    (config : Config Id Heap Body) : Scheduler Id :=
  ⟨config.pending, config.active⟩

/-!
  step changes the heap and one active body's local state.
  spawn returns the fresh child's initial state.
  the body language is otherwise unconstrained.
-/

structure BodySemantics
    (Id : Type uI) (Heap : Type uH) (Body : Type uB) where
  --! 
  step : Id → Heap → Body → Heap → Body → Prop
  spawn : Id → Heap → Body → Id → Heap → Body → Body → Prop
  finished : Id → Body → Prop

def fresh (q : Id) (pending : List Id) (active : Set Id) : Prop :=
  q ∉ pending ∧ q ∉ active

inductive global_step
    [DecidableEq Id]
    (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body) :
    Config Id Heap Body → Config Id Heap Body → Prop
  | start
      (heap : Heap)
      (before after : List Id)
      (active : Set Id)
      (body : Id → Body)
      (b : Id)
      (is_fresh : b ∉ before ++ after)
      (is_eligible : eligible claims b before active) :
      global_step claims semantics
        ⟨heap, before ++ (b :: after), active, body⟩
        ⟨heap, before ++ after, insert b active, body⟩
  | execute
      (heap heap' : Heap)
      (pending : List Id)
      (active : Set Id)
      (body : Id → Body)
      (b : Id)
      (body' : Body)
      (is_active : b ∈ active)
      (steps : semantics.step b heap (body b) heap' body') :
      global_step claims semantics
        ⟨heap, pending, active, body⟩
        ⟨heap', pending, active, Function.update body b body'⟩
  | spawn
      (heap heap' : Heap)
      (pending : List Id)
      (active : Set Id)
      (body : Id → Body)
      (b q : Id)
      (body' child_body : Body)
      (is_active : b ∈ active)
      (is_fresh : fresh q pending active)
      (spawns : semantics.spawn b heap (body b)
        q heap' body' child_body) :
      global_step claims semantics
        ⟨heap, pending, active, body⟩
        ⟨heap', pending ++ [q], active,
          Function.update (Function.update body b body') q child_body⟩
  | finish
      (heap : Heap)
      (pending : List Id)
      (active : Set Id)
      (body : Id → Body)
      (b : Id)
      (is_active : b ∈ active)
      (is_finished : semantics.finished b (body b)) :
      global_step claims semantics
        ⟨heap, pending, active, body⟩
        ⟨heap, pending, active \ {b}, body⟩

abbrev global_reachable
    [DecidableEq Id]
    (claims : Id → Set Cown)
    (semantics : BodySemantics Id Heap Body) :=
  Relation.ReflTransGen (global_step claims semantics)

/-! ## The small projection lemma -/

theorem global_step_projects
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {source target : Config Id Heap Body}
    (step : global_step claims semantics source target) :
    k_step claims source.scheduler target.scheduler := by
  cases step with
  | start heap before after active body b is_fresh is_eligible =>
      exact k_step.start before after active b is_fresh is_eligible
  | execute heap heap' pending active body b body' is_active steps =>
      exact k_step.internal ⟨pending, active⟩
  | spawn heap heap' pending active body b q body' child_body
      is_active is_fresh spawns =>
      exact k_step.spawn pending active q is_fresh.1 is_fresh.2
  | finish heap pending active body b is_active is_finished =>
      exact k_step.finish pending active b is_active

theorem global_reachable_projects
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (reachable : global_reachable claims semantics initial config) :
    scheduler_reachable claims initial.scheduler config.scheduler := by
  induction reachable with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail reachable step ih =>
      exact Relation.ReflTransGen.tail ih (global_step_projects step)

theorem global_reachable_safe
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_safe : safe claims initial.active)
    (reachable : global_reachable claims semantics initial config) :
    safe claims config.active := by
  exact reachable_safe initial_safe (global_reachable_projects reachable)

theorem global_reachable_well_formed
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_well_formed : well_formed initial.scheduler)
    (reachable : global_reachable claims semantics initial config) :
    well_formed config.scheduler := by
  exact reachable_well_formed initial_well_formed
    (global_reachable_projects reachable)

end Boc
