import Boc.Semantics

/-!
# Conditional whole-machine progress

This module assumes progress of behavior bodies.  That assumption is not
used by scheduler safety, race freedom, or acquisition-deadlock freedom.
-/

namespace Boc

variable {Cown Id : Type*} {Heap Body : Type*}
variable [DecidableEq Id]

def BodyProgress
    (semantics : BodySemantics Id Heap Body)
    (config : Config Id Heap Body) : Prop :=
  ∀ b ∈ config.active,
    semantics.finished b (config.body b)
    ∨ (∃ heap' body',
        semantics.step b config.heap (config.body b) heap' body')
    ∨ (∃ q heap' body' childBody,
        Fresh q config.pending config.active ∧
        semantics.spawn b config.heap (config.body b)
          q heap' body' childBody)

def Terminal (config : Config Id Heap Body) : Prop :=
  config.pending = [] ∧ config.active = ∅

/-- A configuration with body progress is terminal or can step.  No
well-formedness is needed: when nothing is active, the head of the pending
queue has nothing ahead of it and nothing to conflict with, so it is always
eligible to start. -/
theorem nonstuck
    {claims : Id → Set Cown}
    {semantics : BodySemantics Id Heap Body}
    {config : Config Id Heap Body}
    (h_progress : BodyProgress semantics config) :
    Terminal config ∨
      ∃ config', Config.StepAny claims semantics config config' := by
  obtain ⟨heap, pending, active, body⟩ := config
  rcases Set.eq_empty_or_nonempty active with rfl | ⟨b, hb⟩
  · cases pending with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons b rest =>
        refine Or.inr ⟨_, _, Config.Step.start (before := []) ?_⟩
        exact ⟨fun a ha => absurd ha (Set.notMem_empty a),
          fun q hq => absurd hq List.not_mem_nil⟩
  · rcases h_progress b hb with is_finished | ⟨heap', body', steps⟩
      | ⟨q, heap', body', childBody, is_fresh, spawns⟩
    · exact Or.inr ⟨_, _, Config.Step.finish hb is_finished⟩
    · exact Or.inr ⟨_, _, Config.Step.execute hb steps⟩
    · exact Or.inr ⟨_, _, Config.Step.spawn hb is_fresh spawns⟩

end Boc
