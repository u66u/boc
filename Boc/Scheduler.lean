import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/-!
Scheduler knows only about behaviors, cown claims, and scheduling. It's abstracted away from
heaps, Locations, or the language used inside a behavior.
-/

namespace Boc

universe uC uI

variable {Cown : Type uC} {Id : Type uI}

/-! Claims and scheduler states -/

def conflicts (claims : Id → Set Cown) (b b' : Id) : Prop :=
  ∃ c, c ∈ claims b ∧ c ∈ claims b'

theorem conflicts_symm {claims : Id → Set Cown} {b b' : Id}
    (h : conflicts claims b b') :
    conflicts claims b' b := by
  rcases h with ⟨c, hb, hb'⟩
  exact ⟨c, hb', hb⟩

structure Scheduler (Id : Type uI) where
  pending : List Id
  active : Set Id

/-!
Behavior identifiers are unique.  `well_formed` records this as a duplicate-
free pending list disjoint from the active set.
-/

def well_formed (scheduler : Scheduler Id) : Prop :=
  scheduler.pending.Nodup ∧
  ∀ ⦃b⦄, b ∈ scheduler.pending → b ∉ scheduler.active

def safe (claims : Id → Set Cown) (active : Set Id) : Prop :=
  ∀ ⦃b b'⦄,
    b ∈ active →
    b' ∈ active →
    b ≠ b' →
    ¬ conflicts claims b b'

def eligible (claims : Id → Set Cown)
    (b : Id)
    (before : List Id)
    (active : Set Id) : Prop :=
  (∀ a, a ∈ active → ¬ conflicts claims b a) ∧
  (∀ q, q ∈ before → ¬ conflicts claims b q)

/-! ## Atomic scheduler transitions -/

/-!
`start` moves one whole behavior into the active set.  A behavior's entire
claim is the fixed set `claims b`, so there is no partial-acquisition state.
There is deliberately no constructor by which an active behavior can acquire
another cown.  `internal` is the projection of an ordinary body step.
-/

inductive k_step (claims : Id → Set Cown) :
    Scheduler Id → Scheduler Id → Prop
  | start
      (before after : List Id)
      (active : Set Id)
      (b : Id)
      (fresh : b ∉ before ++ after)
      (is_eligible : eligible claims b before active) :
      k_step claims
        ⟨before ++ (b :: after), active⟩
        ⟨before ++ after, insert b active⟩
  | internal (scheduler : Scheduler Id) :
      k_step claims scheduler scheduler
  | spawn
      (pending : List Id)
      (active : Set Id)
      (q : Id)
      (fresh_pending : q ∉ pending)
      (fresh_active : q ∉ active) :
      k_step claims
        ⟨pending, active⟩
        ⟨pending ++ [q], active⟩
  | finish
      (pending : List Id)
      (active : Set Id)
      (b : Id)
      (is_active : b ∈ active) :
      k_step claims
        ⟨pending, active⟩
        ⟨pending, active \ {b}⟩

abbrev scheduler_reachable (claims : Id → Set Cown) :=
  Relation.ReflTransGen (k_step claims)

/-! ## Small list facts used by scheduler well-formedness -/

private theorem nodup_remove_middle {α : Type*}
    {before after : List α} {x : α}
    (h_nodup : (before ++ (x :: after)).Nodup) :
    (before ++ after).Nodup := by
  induction before with
  | nil =>
      simp only [List.nil_append] at h_nodup ⊢
      exact (List.nodup_cons.mp h_nodup).2
  | cons y before ih =>
      rw [List.cons_append] at h_nodup ⊢
      rcases List.nodup_cons.mp h_nodup with
        ⟨hy_not_mem, h_tail_nodup⟩
      apply List.nodup_cons.mpr
      constructor
      · intro hy
        apply hy_not_mem
        rw [List.mem_append] at hy ⊢
        rcases hy with hy_before | hy_after
        · exact Or.inl hy_before
        · exact Or.inr (List.mem_cons_of_mem x hy_after)
      · exact ih h_tail_nodup

private theorem nodup_append_singleton {α : Type*}
    {items : List α} {x : α}
    (h_nodup : items.Nodup)
    (h_fresh : x ∉ items) :
    (items ++ [x]).Nodup := by
  induction items with
  | nil =>
      simp
  | cons y items ih =>
      rcases List.nodup_cons.mp h_nodup with
        ⟨hy_not_mem, h_items_nodup⟩
      have hx_ne_y : x ≠ y := by
        intro hxy
        apply h_fresh
        rw [hxy]
        exact List.mem_cons_self
      have hx_not_mem : x ∉ items := by
        intro hx
        exact h_fresh (List.mem_cons_of_mem y hx)
      rw [List.cons_append]
      apply List.nodup_cons.mpr
      constructor
      · intro hy
        rw [List.mem_append] at hy
        rcases hy with hy_items | hy_singleton
        · exact hy_not_mem hy_items
        · exact hx_ne_y (List.mem_singleton.mp hy_singleton).symm
      · exact ih h_items_nodup hx_not_mem

/-! ## Preservation of scheduler invariants -/

theorem safe_of_subset
    {claims : Id → Set Cown} {active active' : Set Id}
    (h_safe : safe claims active)
    (h_subset : active' ⊆ active) :
    safe claims active' := by
  intro b b' hb hb' hne
  exact h_safe (h_subset hb) (h_subset hb') hne

theorem safe_insert
    {claims : Id → Set Cown} {active : Set Id} {b : Id}
    (h_safe : safe claims active)
    (h_free : ∀ a, a ∈ active → ¬ conflicts claims b a) :
    safe claims (insert b active) := by
  intro x y hx hy hxy
  simp only [Set.mem_insert_iff] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact h_free y hy
  · rcases hy with rfl | hy
    · intro h_conflict
      exact h_free x hx (conflicts_symm h_conflict)
    · exact h_safe hx hy hxy

theorem k_step_preserves_safe
    {claims : Id → Set Cown} {source target : Scheduler Id}
    (step : k_step claims source target)
    (h_safe : safe claims source.active) :
    safe claims target.active := by
  cases step with
  | start before after active b fresh is_eligible =>
      exact safe_insert h_safe is_eligible.1
  | internal scheduler =>
      exact h_safe
  | spawn pending active q fresh_pending fresh_active =>
      exact h_safe
  | finish pending active b is_active =>
      exact safe_of_subset h_safe (fun _ h => h.1)

theorem k_step_preserves_well_formed
    {claims : Id → Set Cown} {source target : Scheduler Id}
    (step : k_step claims source target)
    (h_well_formed : well_formed source) :
    well_formed target := by
  cases step with
  | start before after active b fresh is_eligible =>
      constructor
      · exact nodup_remove_middle h_well_formed.1
      · intro x hx_pending hx_active
        simp only [Set.mem_insert_iff] at hx_active
        rcases hx_active with rfl | hx_active
        · exact fresh hx_pending
        · apply h_well_formed.2 ?_ hx_active
          rw [List.mem_append] at hx_pending ⊢
          rcases hx_pending with hx_before | hx_after
          · exact Or.inl hx_before
          · exact Or.inr (List.mem_cons_of_mem b hx_after)
  | internal scheduler =>
      exact h_well_formed
  | spawn pending active q fresh_pending fresh_active =>
      constructor
      · exact nodup_append_singleton h_well_formed.1 fresh_pending
      · intro x hx_pending hx_active
        rw [List.mem_append] at hx_pending
        rcases hx_pending with hx_old | hx_new
        · exact h_well_formed.2 hx_old hx_active
        · rw [List.mem_singleton] at hx_new
          subst x
          exact fresh_active hx_active
  | finish pending active b is_active =>
      constructor
      · exact h_well_formed.1
      · intro x hx_pending hx_active
        exact h_well_formed.2 hx_pending hx_active.1

theorem reachable_safe
    {claims : Id → Set Cown} {initial scheduler : Scheduler Id}
    (initial_safe : safe claims initial.active)
    (reachable : scheduler_reachable claims initial scheduler) :
    safe claims scheduler.active := by
  induction reachable with
  | refl =>
      exact initial_safe
  | tail reachable step ih =>
      exact k_step_preserves_safe step ih

theorem reachable_well_formed
    {claims : Id → Set Cown} {initial scheduler : Scheduler Id}
    (initial_well_formed : well_formed initial)
    (reachable : scheduler_reachable claims initial scheduler) :
    well_formed scheduler := by
  induction reachable with
  | refl =>
      exact initial_well_formed
  | tail reachable step ih =>
      exact k_step_preserves_well_formed step ih

theorem eq_of_active_of_mem_claims
    {claims : Id → Set Cown} {active : Set Id}
    (h_safe : safe claims active)
    {b b' : Id} {c : Cown}
    (hb : b ∈ active)
    (hb' : b' ∈ active)
    (hbc : c ∈ claims b)
    (hb'c : c ∈ claims b') :
    b = b' := by
  classical
  by_contra hne
  exact h_safe hb hb' hne ⟨c, hbc, hb'c⟩

/-! ## The local facts behind conflict ordering -/

theorem active_conflict_blocks_start
    {claims : Id → Set Cown}
    {b a : Id} {before : List Id} {active : Set Id}
    (ha : a ∈ active)
    (h_conflict : conflicts claims b a) :
    ¬ eligible claims b before active := by
  intro is_eligible
  exact is_eligible.1 a ha h_conflict

theorem earlier_conflict_blocks_start
    {claims : Id → Set Cown}
    {b q : Id} {before : List Id} {active : Set Id}
    (hq : q ∈ before)
    (h_conflict : conflicts claims b q) :
    ¬ eligible claims b before active := by
  intro is_eligible
  exact is_eligible.2 q hq h_conflict

end Boc
