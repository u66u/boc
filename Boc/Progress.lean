import Boc.Semantics

/-!
# Conditional whole-machine progress

This module assumes progress of behavior bodies.  That assumption is not used
by scheduler safety, race freedom, or acquisition-deadlock freedom.
-/

namespace Boc

universe uC uI uH uB

variable {Cown : Type uC} {Id : Type uI}
variable {Heap : Type uH} {Body : Type uB}

def body_progress
    (semantics : BodySemantics Id Heap Body)
    (config : Config Id Heap Body) : Prop :=
  ∀ b,
    b ∈ config.active →
      semantics.finished b (config.body b)
      ∨ (∃ heap' body',
          semantics.step b config.heap (config.body b) heap' body')
      ∨ (∃ q heap' body' child_body,
          fresh q config.pending config.active ∧
          semantics.spawn b config.heap (config.body b)
            q heap' body' child_body)

def terminal
    (config : Config Id Heap Body) : Prop :=
  config.pending = [] ∧ ∀ b, b ∉ config.active

theorem nonstuck
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {config : Config Id Heap Body}
    (h_well_formed : well_formed config.scheduler)
    (h_progress : body_progress semantics config) :
    terminal config ∨
      ∃ config', global_step claims semantics config config' := by
  rcases config with ⟨heap, pending, active, body⟩
  by_cases some_active : ∃ b, b ∈ active
  · rcases some_active with ⟨b, hb⟩
    rcases h_progress b hb with is_finished | can_step | can_spawn
    · exact Or.inr ⟨_, global_step.finish
        heap pending active body b hb is_finished⟩
    · rcases can_step with ⟨heap', body', steps⟩
      exact Or.inr ⟨_, global_step.execute
        heap heap' pending active body b body' hb steps⟩
    · rcases can_spawn with
        ⟨q, heap', body', child_body, is_fresh, spawns⟩
      exact Or.inr ⟨_, global_step.spawn
        heap heap' pending active body b q body' child_body
        hb is_fresh spawns⟩
  · cases pending with
    | nil =>
        exact Or.inl ⟨rfl, fun b hb => some_active ⟨b, hb⟩⟩
    | cons b rest =>
        have is_fresh : b ∉ ([] : List Id) ++ rest := by
          simpa only [List.nil_append] using
            (List.nodup_cons.mp h_well_formed.1).1
        have is_eligible : eligible claims b [] active := by
          constructor
          · intro a ha
            exact (some_active ⟨a, ha⟩).elim
          · intro q hq
            exact (List.not_mem_nil hq).elim
        exact Or.inr ⟨_, global_step.start
          heap [] rest active body b is_fresh is_eligible⟩

theorem reachable_nonstuck
    [DecidableEq Id]
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {initial config : Config Id Heap Body}
    (initial_well_formed : well_formed initial.scheduler)
    (reachable : global_reachable claims semantics initial config)
    (h_progress : body_progress semantics config) :
    terminal config ∨
      ∃ config', global_step claims semantics config config' := by
  exact nonstuck
    (global_reachable_well_formed initial_well_formed reachable)
    h_progress

end Boc
