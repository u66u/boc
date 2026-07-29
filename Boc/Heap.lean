import Boc.Scheduler

/-!
# Heap isolation and race freedom

The interface between body execution and the scheduler.
-/

namespace Boc

variable {Cown Id Slot : Type*}

/-- A mutable location tagged with its unique owning cown. -/
abbrev Location (Cown : Type*) (Slot : Type*) := Cown × Slot

def owner (loc : Location Cown Slot) : Cown :=
  loc.1

inductive AccessMode
  | read
  | write

def AccessConflict (left right : AccessMode) : Prop :=
  left = .write ∨ right = .write

/-- `may_access b loc mode` is supplied by the body language for the current
configuration.  Heap isolation says that every such access is covered by the
behavior's claim on the location's unique owner.  The body-language
instantiation must prove that `may_access` covers every actual mutable-memory
access; otherwise the final theorem applies only to the supplied relation. -/
def HeapIsolated (claims : Id → Set Cown)
    (may_access : Id → Location Cown Slot → AccessMode → Prop) : Prop :=
  ∀ ⦃b loc mode⦄,
    may_access b loc mode →
    owner loc ∈ claims b

def HasRace (active : Set Id)
    (may_access : Id → Location Cown Slot → AccessMode → Prop) : Prop :=
  ∃ b b' loc left right,
    b ∈ active ∧
    b' ∈ active ∧
    b ≠ b' ∧
    may_access b loc left ∧
    may_access b' loc right ∧
    AccessConflict left right

/-- Exclusive cown claims prove the stronger fact that distinct active
behaviors cannot access the same mutable location at all, even in read/read
mode. -/
theorem no_active_shared_access
    {claims : Id → Set Cown}
    {active : Set Id}
    {may_access : Id → Location Cown Slot → AccessMode → Prop}
    {b b' : Id} {loc : Location Cown Slot}
    {left right : AccessMode}
    (h_safe : Safe claims active)
    (h_isolated : HeapIsolated claims may_access)
    (hb : b ∈ active)
    (hb' : b' ∈ active)
    (hne : b ≠ b')
    (h_access : may_access b loc left)
    (h_access' : may_access b' loc right) :
    False :=
  h_safe b hb b' hb' hne
    ⟨owner loc, h_isolated h_access, h_isolated h_access'⟩

theorem safe_implies_race_free
    {claims : Id → Set Cown}
    {active : Set Id}
    {may_access : Id → Location Cown Slot → AccessMode → Prop}
    (h_safe : Safe claims active)
    (h_isolated : HeapIsolated claims may_access) :
    ¬ HasRace active may_access :=
  fun ⟨_, _, _, _, _, hb, hb', hne, h_access, h_access', _⟩ =>
    no_active_shared_access h_safe h_isolated hb hb' hne h_access h_access'

end Boc
