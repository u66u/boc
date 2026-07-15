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

