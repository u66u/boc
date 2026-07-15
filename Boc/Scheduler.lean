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

/-! ## Claims and scheduler states -/

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

