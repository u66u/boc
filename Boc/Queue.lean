import Boc.Scheduler
import Mathlib.Data.Finset.Basic

/-!
# Derived queues and the `Finset` boundary

The scheduler kernel speaks `Set Cown`; the protocol machine keeps finite,
sortable claims `Id → Finset Cown`.  This file is the entire boundary
between the two: `conflicts_coe` and `eligible_coe` translate the kernel
predicates through the `Finset → Set` coercion once, and no coercion
reasoning leaks past this file.

`queueOf` is the derived queue a protocol layer maintains explicitly: the
behaviors of an ordered id list that claim a given cown, in list order.
`eligible_iff_forall_cown` restates kernel eligibility per cown — every
claimed cown has no active holder and an empty queue of earlier pending
behaviors — without materializing holder lists.
-/

namespace Boc

variable {Cown Id : Type*}

/-! ## Coercion bridge -/

/-- `Conflicts` through the `Finset → Set` coercion, as `Finset` membership. -/
theorem conflicts_coe (fclaims : Id → Finset Cown) (b b' : Id) :
    Conflicts (fun i => (fclaims i : Set Cown)) b b' ↔
      ∃ c ∈ fclaims b, c ∈ fclaims b' :=
  exists_congr fun _ => and_congr Finset.mem_coe Finset.mem_coe

/-- `Eligible` through the `Finset → Set` coercion, each conjunct stated by
`Finset` membership. -/
theorem eligible_coe (fclaims : Id → Finset Cown) (b : Id)
    (before : List Id) (active : Set Id) :
    Eligible (fun i => (fclaims i : Set Cown)) b before active ↔
      (∀ a ∈ active, ¬ ∃ c ∈ fclaims b, c ∈ fclaims a) ∧
        (∀ q ∈ before, ¬ ∃ c ∈ fclaims b, c ∈ fclaims q) :=
  and_congr
    (forall₂_congr fun a _ => not_congr (conflicts_coe fclaims b a))
    (forall₂_congr fun q _ => not_congr (conflicts_coe fclaims b q))

/-! ## Derived queues -/

variable [DecidableEq Cown]

/-- The queue of a cown: the behaviors of the ordered id list `order` that
claim `c`, in order.  A protocol layer maintains these lists explicitly;
here they are derived, so facts about them are facts about `order`. -/
def queueOf (fclaims : Id → Finset Cown) (order : List Id) (c : Cown) :
    List Id :=
  order.filter (fun b => c ∈ fclaims b)

theorem mem_queueOf {fclaims : Id → Finset Cown} {order : List Id}
    {c : Cown} {b : Id} :
    b ∈ queueOf fclaims order c ↔ b ∈ order ∧ c ∈ fclaims b := by
  simp [queueOf]

theorem queueOf_nil (fclaims : Id → Finset Cown) (c : Cown) :
    queueOf fclaims [] c = [] :=
  rfl

theorem queueOf_cons (fclaims : Id → Finset Cown) (b : Id) (order : List Id)
    (c : Cown) :
    queueOf fclaims (b :: order) c =
      if c ∈ fclaims b then b :: queueOf fclaims order c
      else queueOf fclaims order c := by
  simp [queueOf, List.filter_cons]

theorem queueOf_append (fclaims : Id → Finset Cown) (order₁ order₂ : List Id)
    (c : Cown) :
    queueOf fclaims (order₁ ++ order₂) c =
      queueOf fclaims order₁ c ++ queueOf fclaims order₂ c :=
  List.filter_append order₁ order₂

theorem queueOf_nodup {fclaims : Id → Finset Cown} {order : List Id} {c : Cown}
    (h_nodup : order.Nodup) : (queueOf fclaims order c).Nodup :=
  h_nodup.filter _

theorem queueOf_eq_nil_iff {fclaims : Id → Finset Cown} {order : List Id}
    {c : Cown} :
    queueOf fclaims order c = [] ↔ ∀ b ∈ order, c ∉ fclaims b := by
  simp [queueOf]

/-! ## Eligibility per cown -/

/-- Kernel eligibility is a per-cown condition: `b` may start iff every cown
it claims has no active holder and an empty queue among the earlier pending
behaviors.  This is the "`b` heads every queue it needs" fact, expressed
without materializing holder lists. -/
theorem eligible_iff_forall_cown (fclaims : Id → Finset Cown) (b : Id)
    (before : List Id) (active : Set Id) :
    Eligible (fun i => (fclaims i : Set Cown)) b before active ↔
      ∀ c ∈ fclaims b,
        (∀ a ∈ active, c ∉ fclaims a) ∧ queueOf fclaims before c = [] := by
  rw [eligible_coe]
  constructor
  · rintro ⟨h_active, h_before⟩ c hc
    exact ⟨fun a ha hca => h_active a ha ⟨c, hc, hca⟩,
      queueOf_eq_nil_iff.mpr fun q hq hcq => h_before q hq ⟨c, hc, hcq⟩⟩
  · intro h_cown
    exact ⟨fun a ha ⟨c, hc, hca⟩ => (h_cown c hc).1 a ha hca,
      fun q hq ⟨c, hc, hcq⟩ => queueOf_eq_nil_iff.mp (h_cown c hc).2 q hq hcq⟩

end Boc
