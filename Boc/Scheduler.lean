import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/-!
Scheduler knows only about behaviours, cown claims, and scheduling. It's abstracted away from
heaps, Locations, or the language used inside a behaviour.
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
