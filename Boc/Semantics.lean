import Boc.Scheduler
import Mathlib.Logic.Function.Basic

namespace Boc

universe uC uI uH uB

variable {Cown : Type uC} {Id : Type uI}
variable {Heap : Type uH} {Body : Type uB}

structure Config
    (Id : Type uI) (Heap : Type uH) (Body : Type uB) where
  heap : Heap
  pending : List Id
  active : Set Id
  body : Id → Body

def Config.scheduler
    (config : Config Id Heap Body) : Scheduler Id :=
  ⟨config.pending, config.active⟩

