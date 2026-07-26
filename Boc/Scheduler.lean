import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/-!
# Scheduler kernel

The scheduler knows only about behaviors, cown claims, and scheduling.  It is
abstracted away from heaps, locations, and the language used inside a
behavior.
-/

namespace Boc

variable {Cown Id : Type*}

/-! ## Claims and scheduler states -/

/-- Two behaviors conflict when their claims share a cown.  This is
`¬ Disjoint (claims b) (claims b')`; the explicit witness form is kept
because it is what the proofs manipulate. -/
def Conflicts (claims : Id → Set Cown) (b b' : Id) : Prop :=
  ∃ c, c ∈ claims b ∧ c ∈ claims b'

theorem Conflicts.symm {claims : Id → Set Cown} {b b' : Id} :
    Conflicts claims b b' → Conflicts claims b' b :=
  fun ⟨c, hb, hb'⟩ => ⟨c, hb', hb⟩

structure Scheduler (Id : Type*) where
  pending : List Id
  active : Set Id

/-- Behavior identifiers are unique: the pending list is duplicate-free and
disjoint from the active set. -/
def Scheduler.WellFormed (scheduler : Scheduler Id) : Prop :=
  scheduler.pending.Nodup ∧
  ∀ b ∈ scheduler.pending, b ∉ scheduler.active

/-- No two distinct active behaviors share a cown.  Equivalently,
`active.PairwiseDisjoint claims`; the explicit form is kept for readability. -/
def Safe (claims : Id → Set Cown) (active : Set Id) : Prop :=
  ∀ b ∈ active, ∀ b' ∈ active, b ≠ b' → ¬ Conflicts claims b b'

/-- `q` is fresh for the current scheduler state.  This permits reuse of the
identifier of an already finished behavior; nothing proved here depends on
uniqueness across time. -/
def Fresh (q : Id) (pending : List Id) (active : Set Id) : Prop :=
  q ∉ pending ∧ q ∉ active

/-- A pending behavior may start only if it conflicts with no active behavior
and no earlier pending behavior. -/
def Eligible (claims : Id → Set Cown) (b : Id)
    (before : List Id) (active : Set Id) : Prop :=
  (∀ a ∈ active, ¬ Conflicts claims b a) ∧
  (∀ q ∈ before, ¬ Conflicts claims b q)

/-! ## Atomic scheduler transitions -/

/-- Observable scheduler events.  The `parent` of a `spawn` is pure label
data: no kernel rule constrains it.  It exists so that refinements which
know the spawning behavior can record it. -/
inductive Scheduler.Event (Id : Type*)
  | spawn (parent : Option Id) (b : Id)
  | start (b : Id)
  | finish (b : Id)

/-- `start` moves one whole behavior into the active set.  A behavior's
entire claim is the fixed set `claims b`, so there is no partial-acquisition
state, and there is deliberately no constructor by which an active behavior
can acquire another cown.  Every step is labeled with the event it performs;
there is no silent step at this level.

Identifier freshness is not a side condition of `start`; it is carried by
the `WellFormed` invariant. -/
inductive Scheduler.Step (claims : Id → Set Cown) :
    Scheduler.Event Id → Scheduler Id → Scheduler Id → Prop
  | start {before after : List Id} {active : Set Id} {b : Id}
      (is_eligible : Eligible claims b before active) :
      Scheduler.Step claims (.start b)
        ⟨before ++ (b :: after), active⟩
        ⟨before ++ after, insert b active⟩
  | spawn {parent : Option Id} {pending : List Id} {active : Set Id} {q : Id}
      (is_fresh : Fresh q pending active) :
      Scheduler.Step claims (.spawn parent q)
        ⟨pending, active⟩
        ⟨pending ++ [q], active⟩
  | finish {pending : List Id} {active : Set Id} {b : Id}
      (is_active : b ∈ active) :
      Scheduler.Step claims (.finish b)
        ⟨pending, active⟩
        ⟨pending, active \ {b}⟩

/-- Some scheduler step fires, whatever its event. -/
abbrev Scheduler.StepAny (claims : Id → Set Cown)
    (scheduler scheduler' : Scheduler Id) : Prop :=
  ∃ e, Scheduler.Step claims e scheduler scheduler'

abbrev Scheduler.Reachable (claims : Id → Set Cown) :=
  Relation.ReflTransGen (Scheduler.StepAny claims)

/-! ## Preservation of scheduler invariants -/

theorem Safe.mono
    {claims : Id → Set Cown} {active active' : Set Id}
    (h_safe : Safe claims active)
    (h_subset : active' ⊆ active) :
    Safe claims active' :=
  fun b hb b' hb' hne => h_safe b (h_subset hb) b' (h_subset hb') hne

theorem Safe.insert
    {claims : Id → Set Cown} {active : Set Id} {b : Id}
    (h_safe : Safe claims active)
    (h_free : ∀ a ∈ active, ¬ Conflicts claims b a) :
    Safe claims (insert b active) := by
  intro x hx y hy hxy
  rcases Set.mem_insert_iff.mp hx with rfl | hxa
  · rcases Set.mem_insert_iff.mp hy with rfl | hya
    · exact absurd rfl hxy
    · exact h_free y hya
  · rcases Set.mem_insert_iff.mp hy with rfl | hya
    · exact fun h_conflict => h_free x hxa h_conflict.symm
    · exact h_safe x hxa y hya hxy

theorem Scheduler.Step.preserves_safe
    {claims : Id → Set Cown} {e : Scheduler.Event Id}
    {source target : Scheduler Id}
    (step : Scheduler.Step claims e source target)
    (h_safe : Safe claims source.active) :
    Safe claims target.active := by
  cases step with
  | start is_eligible => exact h_safe.insert is_eligible.1
  | spawn is_fresh => exact h_safe
  | finish is_active => exact h_safe.mono fun _ h => h.1

theorem Scheduler.Step.preserves_wellFormed
    {claims : Id → Set Cown} {e : Scheduler.Event Id}
    {source target : Scheduler Id}
    (step : Scheduler.Step claims e source target)
    (h_wf : source.WellFormed) :
    target.WellFormed := by
  cases step with
  | @start before after active b is_eligible =>
      obtain ⟨hb_fresh, h_nodup⟩ :=
        List.nodup_cons.mp (List.nodup_middle.mp h_wf.1)
      refine ⟨h_nodup, fun x hx hx_active => ?_⟩
      rcases Set.mem_insert_iff.mp hx_active with rfl | hxa
      · exact hb_fresh hx
      · refine h_wf.2 x ?_ hxa
        rw [List.mem_append] at hx ⊢
        exact hx.imp id (List.mem_cons_of_mem b)
  | @spawn parent pending active q is_fresh =>
      refine ⟨h_wf.1.append (List.nodup_singleton q)
        (List.disjoint_singleton.mpr is_fresh.1), fun x hx => ?_⟩
      rcases List.mem_append.mp hx with hxp | hxq
      · exact h_wf.2 x hxp
      · obtain rfl := List.mem_singleton.mp hxq
        exact is_fresh.2
  | finish is_active =>
      exact ⟨h_wf.1, fun x hx hx_active => h_wf.2 x hx hx_active.1⟩

theorem Scheduler.reachable_safe
    {claims : Id → Set Cown} {initial scheduler : Scheduler Id}
    (initial_safe : Safe claims initial.active)
    (reachable : Scheduler.Reachable claims initial scheduler) :
    Safe claims scheduler.active := by
  induction reachable with
  | refl => exact initial_safe
  | tail _ step ih =>
      obtain ⟨_, hstep⟩ := step
      exact hstep.preserves_safe ih

theorem Scheduler.reachable_wellFormed
    {claims : Id → Set Cown} {initial scheduler : Scheduler Id}
    (initial_wf : initial.WellFormed)
    (reachable : Scheduler.Reachable claims initial scheduler) :
    scheduler.WellFormed := by
  induction reachable with
  | refl => exact initial_wf
  | tail _ step ih =>
      obtain ⟨_, hstep⟩ := step
      exact hstep.preserves_wellFormed ih

/-- On a safe active set, a cown pins down its holder uniquely. -/
theorem Safe.eq_of_mem_claims
    {claims : Id → Set Cown} {active : Set Id}
    (h_safe : Safe claims active)
    {b b' : Id} {c : Cown}
    (hb : b ∈ active) (hb' : b' ∈ active)
    (hbc : c ∈ claims b) (hb'c : c ∈ claims b') :
    b = b' := by
  by_contra hne
  exact h_safe b hb b' hb' hne ⟨c, hbc, hb'c⟩

/-! ## The local facts behind conflict ordering -/

theorem active_conflict_blocks_start
    {claims : Id → Set Cown}
    {b a : Id} {before : List Id} {active : Set Id}
    (ha : a ∈ active)
    (h_conflict : Conflicts claims b a) :
    ¬ Eligible claims b before active :=
  fun is_eligible => is_eligible.1 a ha h_conflict

theorem earlier_conflict_blocks_start
    {claims : Id → Set Cown}
    {b q : Id} {before : List Id} {active : Set Id}
    (hq : q ∈ before)
    (h_conflict : Conflicts claims b q) :
    ¬ Eligible claims b before active :=
  fun is_eligible => is_eligible.2 q hq h_conflict

end Boc
