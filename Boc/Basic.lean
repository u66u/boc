import Mathlib

namespace BoC

abbrev Claims (Cown : Type*) := Cown → Prop
abbrev Active (Id : Type*) := Id → Prop
abbrev Loc (Cown Slot : Type*) := Cown × Slot

def owner {Cown Slot : Type*} (ℓ : Loc Cown Slot) : Cown :=
  ℓ.1

def add_active {Id : Type*} (b : Id) (A : Active Id) : Active Id :=
  fun x => x = b ∨ A x

def drop_active {Id : Type*} (b : Id) (A : Active Id) : Active Id :=
  fun x => A x ∧ x ≠ b
