import Boc.Scheduler

/-!
interface between body execution and the scheduler.
-/

namespace Boc

universe uC uI uS

variable {Cown : Type uC} {Id : Type uI} {Slot : Type uS}

-- Tagged mutable Locations for cowns
abbrev Location (Cown : Type uC) (Slot : Type uS) := Cown × Slot

def owner (loc : Location Cown Slot) : Cown :=
  loc.1

inductive access_mode
  | read
  | write
  deriving DecidableEq

def access_conflict (left right : access_mode) : Prop :=
  left = .write ∨ right = .write

/-!
`may_access b loc mode` is supplied by the body language for the current
configuration.  Heap isolation says that every such access is covered by the
behavior's claim on the Location's unique owner.  The body-language
instantiation must prove that `may_access` covers every actual mutable-memory
access; otherwise the final theorem applies only to the supplied relation.
-/

def heap_isolated (claims : Id → Set Cown)
    (may_access : Id → Location Cown Slot → access_mode → Prop) : Prop :=
  ∀ ⦃b loc mode⦄,
    may_access b loc mode →
    owner loc ∈ claims b

def has_race (active : Set Id)
    (may_access : Id → Location Cown Slot → access_mode → Prop) : Prop :=
  ∃ b b' loc left right,
    b ∈ active ∧
    b' ∈ active ∧
    b ≠ b' ∧
    may_access b loc left ∧
    may_access b' loc right ∧
    access_conflict left right

/-!
Exclusive cown claims prove the stronger fact that distinct active behaviors
cannot access the same mutable Location at all, even in read/read mode.
-/

theorem no_active_shared_access
    {claims : Id → Set Cown}
    {active : Set Id}
    {may_access : Id → Location Cown Slot → access_mode → Prop}
    {b b' : Id} {loc : Location Cown Slot}
    {left right : access_mode}
    (h_safe : safe claims active)
    (h_isolated : heap_isolated claims may_access)
    (hb : b ∈ active)
    (hb' : b' ∈ active)
    (hne : b ≠ b')
    (h_access : may_access b loc left)
    (h_access' : may_access b' loc right) :
    False := by
  exact h_safe hb hb' hne
    ⟨owner loc, h_isolated h_access, h_isolated h_access'⟩

theorem safe_implies_race_free
    {claims : Id → Set Cown}
    {active : Set Id}
    {may_access : Id → Location Cown Slot → access_mode → Prop}
    (h_safe : safe claims active)
    (h_isolated : heap_isolated claims may_access) :
    ¬ has_race active may_access := by
  intro race
  rcases race with
    ⟨b, b', loc, left, right,
      hb, hb', hne, h_access, h_access', _⟩
  exact no_active_shared_access
    h_safe h_isolated hb hb' hne h_access h_access'

end Boc
