import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

/-!
# Protocol machine

The queue protocol behind behaviour-oriented concurrency, as implemented by
`verona-rt`: a behaviour claims a finite set of cowns, sorts them by a global
order, and walks that order acquiring one cown at a time.  Acquiring a cown
means atomically appending yourself to its queue and learning your
predecessor; you may move to the next cown only once that predecessor has
itself finished acquiring.  A behaviour runs when it heads every queue it
claimed, and afterwards pops itself off those queues one at a time.

Two events are linearization points and nothing else happens at them:

* `acquireDone` is the **kernel spawn** point.  It fires when the acquire
  loop has finished, and its only effect is to append the behaviour to the
  ghost field `order`.
* `bodyDone` is the **kernel finish** point.  It moves a behaviour from
  `active` to `done`; the per-cown releases that follow are separate steps.

`order` and `used` are bookkeeping.  `used` records that identifiers are never
reused and nothing reads it but the freshness gate of `create`.  `order` is the
sequence of acquire completions, and it is the sequence the queues are proved
to refine (`Inv.queue_order_refines_order`).  Membership in `order` is read by
the chaining gate, and deliberately so: `b ∈ order` is the runtime's
per-behaviour `scheduled` flag, which is exactly what a predecessor is waited
on for.  Its list structure is ghost; only its membership is observed.
-/

namespace Boc

variable {Cown Id : Type*}

/-- The cowns a behaviour claims, in the global acquisition order.  A
behaviour acquires exactly this list, left to right. -/
def sortedClaims [LinearOrder Cown] (fclaims : Id → Finset Cown) (b : Id) :
    List Cown :=
  (fclaims b).sort (· ≤ ·)

theorem mem_sortedClaims [LinearOrder Cown] {fclaims : Id → Finset Cown}
    {b : Id} {c : Cown} : c ∈ sortedClaims fclaims b ↔ c ∈ fclaims b :=
  Finset.mem_sort (· ≤ ·)

theorem sortedClaims_nodup [LinearOrder Cown] (fclaims : Id → Finset Cown)
    (b : Id) : (sortedClaims fclaims b).Nodup :=
  Finset.sort_nodup _ _

namespace Protocol

/-! ## Positions inside a list

Two list notions carry the whole ordering argument.  `Precedes` is strict
"earlier than" inside the ghost order, and `ahead` is the set of behaviours
queued in front of a given one.  Queues only ever grow at the tail and shrink
at the head, so a `takeWhile` prefix is the shape that survives every step.
-/

/-- `x` occurs somewhere strictly before `y` in `l`. -/
def Precedes (l : List Id) (x y : Id) : Prop :=
  [x, y].Sublist l

theorem Precedes.mem_left {l : List Id} {x y : Id} (h : Precedes l x y) :
    x ∈ l :=
  h.subset List.mem_cons_self

variable [DecidableEq Id]

/-- The behaviours queued ahead of `b`: the prefix of `l` strictly before
`b`'s first occurrence. -/
def ahead (l : List Id) (b : Id) : List Id :=
  l.takeWhile fun x => decide (x ≠ b)

@[simp] theorem ahead_cons_self (b : Id) (l : List Id) : ahead (b :: l) b = [] := by
  simp [ahead]

theorem ahead_cons_of_ne {a b : Id} (h : a ≠ b) (l : List Id) :
    ahead (a :: l) b = a :: ahead l b := by
  simp [ahead, h]

theorem ahead_prefix (l : List Id) (b : Id) : ahead l b <+: l :=
  List.takeWhile_prefix _

theorem mem_of_mem_ahead {l : List Id} {b x : Id} (h : x ∈ ahead l b) : x ∈ l :=
  (ahead_prefix l b).subset h

/-- Appending at the tail leaves the behaviours ahead of an existing member
untouched: the whole point of a tail-only queue. -/
theorem ahead_append_of_mem {l l' : List Id} {b : Id} (h : b ∈ l) :
    ahead (l ++ l') b = ahead l b := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a t ih =>
      rcases eq_or_ne a b with rfl | hab
      · simp
      · rw [List.cons_append, ahead_cons_of_ne hab, ahead_cons_of_ne hab,
          ih ((List.mem_cons.mp h).resolve_left fun hb => hab hb.symm)]

theorem ahead_eq_of_notMem {u v : List Id} {b : Id} (h : b ∉ u) :
    ahead (u ++ b :: v) b = u := by
  induction u with
  | nil => simp
  | cons a t ih =>
      have hab : a ≠ b := fun hb => h (by subst hb; exact List.mem_cons_self)
      rw [List.cons_append, ahead_cons_of_ne hab,
        ih fun ht => h (List.mem_cons_of_mem a ht)]

/-- Inside a duplicate-free list, "earlier than `b`" and "ahead of `b`"
agree.  This is the only place the two notions meet. -/
theorem mem_ahead_of_precedes {l : List Id} {x b : Id}
    (h_nodup : l.Nodup) (h : Precedes l x b) : x ∈ ahead l b := by
  induction l with
  | nil => exact absurd h (by simp [Precedes])
  | cons a t ih =>
      obtain ⟨h_head, h_tail⟩ := List.nodup_cons.mp h_nodup
      cases h with
      | cons _ h' =>
          have hab : a ≠ b := fun hb => h_head (by
            subst hb; exact h'.subset (List.mem_cons_of_mem _ List.mem_cons_self))
          rw [ahead_cons_of_ne hab]
          exact List.mem_cons_of_mem a (ih h_tail h')
      | cons_cons _ h' =>
          have hxb : x ≠ b := fun hb => h_head (by
            subst hb; exact h'.subset List.mem_cons_self)
          rw [ahead_cons_of_ne hxb]
          exact List.mem_cons_self

/-! ## States and events -/

/-- A protocol state.  `queues c` is the FIFO of cown `c`, head first;
`progress b` counts the exchanges `b` has completed, i.e. how far into
`sortedClaims fclaims b` it has walked.  `order` and `used` are ghost. -/
structure State (Cown Id : Type*) where
  queues : Cown → List Id
  progress : Id → ℕ
  parentOf : Id → Option Id
  active : Set Id
  done : Set Id
  order : List Id
  used : Finset Id

/-- Observable protocol events.  `create` and `acquireDone` carry the parent
as label data, exactly as `Scheduler.Event.spawn` does. -/
inductive Event (Cown Id : Type*)
  | create (parent : Option Id) (b : Id)
  | exchange (b : Id) (c : Cown)
  | acquireDone (parent : Option Id) (b : Id)
  | run (b : Id)
  | bodyDone (b : Id)
  | release (b : Id) (c : Cown)

/-- The chaining gate at cown `c`: whoever sits immediately ahead of `b` in
`c`'s queue, if anybody does, has already passed its acquire linearization
point.  This is the `wait until the predecessor is scheduled` of the real
acquire loop; "scheduled" is `∈ order`. -/
def Chained (s : State Cown Id) (b : Id) (c : Cown) : Prop :=
  ∀ p, (ahead (s.queues c) b).getLast? = some p → p ∈ s.order

/-- The chaining gate at the cown `b` acquired most recently, vacuous before
`b`'s first exchange.  Both `exchange` and `acquireDone` are gated by it: the
former to move on to the next cown, the latter to finish the loop. -/
def ChainedPrev [LinearOrder Cown] (fclaims : Id → Finset Cown)
    (s : State Cown Id) (b : Id) : Prop :=
  ∀ c, ((sortedClaims fclaims b).take (s.progress b)).getLast? = some c →
    Chained s b c

variable [LinearOrder Cown]

/-- Atomic protocol transitions.  Every rule touches at most one cown's
queue. -/
inductive Step (fclaims : Id → Finset Cown) :
    Event Cown Id → State Cown Id → State Cown Id → Prop
  /-- Allocate a fresh identifier.  Gate: the identifier was never used. -/
  | create {s : State Cown Id} {parent : Option Id} {b : Id}
      (is_fresh : b ∉ s.used) :
      Step fclaims (.create parent b) s
        { s with
          progress := Function.update s.progress b 0
          parentOf := Function.update s.parentOf b parent
          used := insert b s.used }
  /-- Acquire the next claimed cown by appending to its queue.  Gate: `c` is
  the next cown in the global order, `b` is not already queued on it, and the
  behaviour immediately ahead of `b` on the previously acquired cown has
  passed its linearization point. -/
  | exchange {s : State Cown Id} {b : Id} {c : Cown}
      (is_used : b ∈ s.used)
      (is_next : (sortedClaims fclaims b)[s.progress b]? = some c)
      (is_new : b ∉ s.queues c)
      (chained : ChainedPrev fclaims s b) :
      Step fclaims (.exchange b c) s
        { s with
          queues := Function.update s.queues c (s.queues c ++ [b])
          progress := Function.update s.progress b (s.progress b + 1) }
  /-- The kernel-spawn linearization point: the acquire loop is over and the
  behaviour joins the ghost completion order.  Gate: every claimed cown has
  been exchanged, the behaviour has not already finished acquiring, and the
  behaviour immediately ahead of `b` on its last cown has passed its own
  linearization point. -/
  | acquireDone {s : State Cown Id} {parent : Option Id} {b : Id}
      (is_used : b ∈ s.used)
      (is_parent : s.parentOf b = parent)
      (is_full : s.progress b = (sortedClaims fclaims b).length)
      (is_new : b ∉ s.order)
      (chained : ChainedPrev fclaims s b) :
      Step fclaims (.acquireDone parent b) s { s with order := s.order ++ [b] }
  /-- Start the body.  Gate: the behaviour has passed its acquire
  linearization point, has not started or finished, and heads every queue it
  claimed. -/
  | run {s : State Cown Id} {b : Id}
      (is_acquired : b ∈ s.order)
      (not_active : b ∉ s.active)
      (not_done : b ∉ s.done)
      (heads : ∀ c ∈ fclaims b, (s.queues c).head? = some b) :
      Step fclaims (.run b) s { s with active := insert b s.active }
  /-- The kernel-finish linearization point: the body is over, the releases
  are not.  Gate: the behaviour is running. -/
  | bodyDone {s : State Cown Id} {b : Id}
      (is_active : b ∈ s.active) :
      Step fclaims (.bodyDone b) s
        { s with active := s.active \ {b}, done := insert b s.done }
  /-- Release one cown, waking its successor.  Gate: the body is over and the
  behaviour heads that cown's queue. -/
  | release {s : State Cown Id} {b : Id} {c : Cown}
      (is_done : b ∈ s.done)
      (is_head : (s.queues c).head? = some b) :
      Step fclaims (.release b c) s
        { s with queues := Function.update s.queues c (s.queues c).tail }

/-- Some protocol step fires, whatever its event. -/
abbrev StepAny (fclaims : Id → Finset Cown) (s s' : State Cown Id) : Prop :=
  ∃ e, Step fclaims e s s'

abbrev Reachable (fclaims : Id → Finset Cown) :=
  Relation.ReflTransGen (StepAny fclaims)

/-! ## The protocol invariant -/

/-- The protocol invariant.  Fields are in dependency order: each preservation
proof consumes only fields above it, the one exception being that
`queue_linearizes` and `settled` are established simultaneously — each one's
preservation consumes the other at the pre-state, which is sound because both
are read before the step and written after it.

`queue_linearizes` is the keystone: inside every queue, a behaviour that has
passed its linearization point is preceded, in the ghost order, by everybody
queued ahead of it.  `settled` is what the chaining gate accumulates as the
acquire loop walks the claim list, and is what makes `queue_linearizes`
inductive at `acquireDone`. -/
structure Inv (fclaims : Id → Finset Cown) (s : State Cown Id) : Prop where
  progress_le : ∀ b, s.progress b ≤ (sortedClaims fclaims b).length
  progress_used : ∀ b, s.progress b ≠ 0 → b ∈ s.used
  queue_used : ∀ c, ∀ b ∈ s.queues c, b ∈ s.used
  order_used : ∀ b ∈ s.order, b ∈ s.used
  queue_taken : ∀ c, ∀ b ∈ s.queues c,
    c ∈ (sortedClaims fclaims b).take (s.progress b)
  queue_nodup : ∀ c, (s.queues c).Nodup
  order_nodup : s.order.Nodup
  order_progress : ∀ b ∈ s.order, s.progress b = (sortedClaims fclaims b).length
  queue_linearizes : ∀ c, ∀ b ∈ s.order, b ∈ s.queues c →
    ∀ x ∈ ahead (s.queues c) b, Precedes s.order x b
  settled : ∀ b, ∀ c ∈ ((sortedClaims fclaims b).take (s.progress b)).dropLast,
    b ∈ s.queues c → ∀ x ∈ ahead (s.queues c) b, x ∈ s.order
  active_done_disjoint : ∀ b ∈ s.active, b ∉ s.done
  active_order : ∀ b ∈ s.active, b ∈ s.order
  done_order : ∀ b ∈ s.done, b ∈ s.order
  active_heads : ∀ b ∈ s.active, ∀ c ∈ fclaims b, (s.queues c).head? = some b
  done_heads : ∀ b ∈ s.done, ∀ c, b ∈ s.queues c → (s.queues c).head? = some b

/-- The empty protocol state: nothing created, every queue empty. -/
def State.initial (Cown Id : Type*) : State Cown Id where
  queues := fun _ => []
  progress := fun _ => 0
  parentOf := fun _ => none
  active := ∅
  done := ∅
  order := []
  used := ∅

variable {fclaims : Id → Finset Cown} {s s' : State Cown Id}

theorem Inv.initial : Inv fclaims (State.initial Cown Id) := by
  constructor <;> simp [State.initial, ahead]

/-- A queue member claims that cown. -/
theorem Inv.queue_mem_claims (inv : Inv fclaims s) (c : Cown) {b : Id}
    (hb : b ∈ s.queues c) : c ∈ fclaims b :=
  mem_sortedClaims.mp (List.mem_of_mem_take (inv.queue_taken c b hb))

/-- The chaining gate amplifies from the immediate predecessor to the whole
prefix: the keystone turns "my predecessor is linearized" into "everybody
ahead of me is linearized". -/
theorem Inv.ahead_subset_order (inv : Inv fclaims s) {b : Id} {c : Cown}
    (h_chain : Chained s b c) : ∀ x ∈ ahead (s.queues c) b, x ∈ s.order := by
  intro x hx
  rcases List.eq_nil_or_concat (ahead (s.queues c) b) with h_nil | ⟨u, p, h_eq⟩
  · rw [h_nil] at hx; exact absurd hx List.not_mem_nil
  · rw [List.concat_eq_append] at h_eq
    have h_last : (ahead (s.queues c) b).getLast? = some p := by
      rw [h_eq]; exact List.getLast?_concat
    have hp : p ∈ s.order := h_chain p h_last
    have hpq : p ∈ s.queues c := mem_of_mem_ahead (by rw [h_eq]; simp)
    have h_split : s.queues c =
        u ++ p :: (s.queues c).dropWhile fun y => decide (y ≠ b) := by
      conv_lhs => rw [← List.takeWhile_append_dropWhile
        (p := fun y => decide (y ≠ b)) (l := s.queues c)]
      rw [show (s.queues c).takeWhile (fun y => decide (y ≠ b)) = u ++ [p] from h_eq]
      simp
    have h_nodup : (u ++ p :: (s.queues c).dropWhile fun y => decide (y ≠ b)).Nodup := by
      rw [← h_split]; exact inv.queue_nodup c
    have hpu : p ∉ u := fun hmem =>
      (List.nodup_append.mp h_nodup).2.2 p hmem p List.mem_cons_self rfl
    have h_ahead : ahead (s.queues c) p = u := by
      conv_lhs => rw [h_split]
      exact ahead_eq_of_notMem hpu
    rw [h_eq, List.mem_append] at hx
    rcases hx with hxu | hxp
    · exact (inv.queue_linearizes c p hp hpq x (h_ahead ▸ hxu)).mem_left
    · rw [List.mem_singleton.mp hxp]; exact hp

/-- Everybody queued ahead of `b` on a cown `b` currently holds has passed
its linearization point.  The most recently acquired cown is covered by the
chaining gate, every earlier one by `settled`. -/
theorem Inv.ahead_subset_order_of_mem (inv : Inv fclaims s) {b : Id} {c : Cown}
    (h_gate : ChainedPrev fclaims s b) (hbq : b ∈ s.queues c) :
    ∀ x ∈ ahead (s.queues c) b, x ∈ s.order := by
  have hc := inv.queue_taken c b hbq
  rcases h_last : ((sortedClaims fclaims b).take (s.progress b)).getLast? with
    _ | clast
  · rw [List.getLast?_eq_none_iff] at h_last
    rw [h_last] at hc
    exact absurd hc List.not_mem_nil
  · rcases eq_or_ne c clast with rfl | hne
    · exact inv.ahead_subset_order (h_gate c h_last)
    · obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp h_last
      refine inv.settled b c ?_ hbq
      rw [hu] at hc ⊢
      rw [List.dropLast_concat]
      exact (List.mem_append.mp hc).resolve_right fun h =>
        hne (List.mem_singleton.mp h)

omit [LinearOrder Cown] in
/-- A cown reached at index `n` of a duplicate-free list is not among the
first `n`. -/
theorem notMem_take_of_getElem? {l : List Cown} {n : ℕ} {c : Cown}
    (h_nodup : l.Nodup) (h : l[n]? = some c) : c ∉ l.take n := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact fun hmem => List.disjoint_take_drop h_nodup (Nat.le_refl n) hmem
    (by rw [List.drop_eq_getElem_cons hn]; exact List.mem_cons_self)

omit [LinearOrder Cown] in
/-- `take (n+1)` of a list is `take n` with the `n`-th entry appended. -/
theorem take_succ_eq_concat {l : List Cown} {n : ℕ} {c : Cown}
    (h : l[n]? = some c) : l.take (n + 1) = l.take n ++ [c] := by
  rw [List.take_add_one, h]; rfl

/-! ## Preservation, one field at a time -/

theorem Inv.preserve_progress_le {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ b, s'.progress b ≤ (sortedClaims fclaims b).length := by
  cases step with
  | @create s parent b is_fresh =>
      intro x
      rcases eq_or_ne x b with rfl | hne
      · simp
      · simpa [Function.update_of_ne hne] using inv.progress_le x
  | @exchange s b c is_used is_next is_new chained =>
      intro x
      rcases eq_or_ne x b with rfl | hne
      · obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp is_next
        simp only [Function.update_self]
        exact hlt
      · simpa [Function.update_of_ne hne] using inv.progress_le x
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.progress_le
  | @run s b is_acquired not_active not_done heads => exact inv.progress_le
  | @bodyDone s b is_active => exact inv.progress_le
  | @release s b c is_done is_head => exact inv.progress_le

theorem Inv.preserve_progress_used {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ b, s'.progress b ≠ 0 → b ∈ s'.used := by
  cases step with
  | @create s parent b is_fresh =>
      intro x hx
      rcases eq_or_ne x b with rfl | hne
      · simp at hx
      · exact Finset.mem_insert_of_mem
          (inv.progress_used x (by simpa [Function.update_of_ne hne] using hx))
  | @exchange s b c is_used is_next is_new chained =>
      intro x hx
      rcases eq_or_ne x b with rfl | hne
      · exact is_used
      · exact inv.progress_used x (by simpa [Function.update_of_ne hne] using hx)
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.progress_used
  | @run s b is_acquired not_active not_done heads => exact inv.progress_used
  | @bodyDone s b is_active => exact inv.progress_used
  | @release s b c is_done is_head => exact inv.progress_used

theorem Inv.preserve_queue_used {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ c, ∀ b ∈ s'.queues c, b ∈ s'.used := by
  cases step with
  | @create s parent b is_fresh =>
      exact fun c x hx => Finset.mem_insert_of_mem (inv.queue_used c x hx)
  | @exchange s b c is_used is_next is_new chained =>
      intro c' x hx
      rcases eq_or_ne c' c with rfl | hne
      · simp only [Function.update_self, List.mem_append] at hx
        rcases hx with hx | hx
        · exact inv.queue_used c' x hx
        · rw [List.mem_singleton.mp hx]; exact is_used
      · exact inv.queue_used c' x (by simpa only [Function.update_of_ne hne] using hx)
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.queue_used
  | @run s b is_acquired not_active not_done heads => exact inv.queue_used
  | @bodyDone s b is_active => exact inv.queue_used
  | @release s b c is_done is_head =>
      intro c' x hx
      rcases eq_or_ne c' c with rfl | hne
      · simp only [Function.update_self] at hx
        exact inv.queue_used c' x (List.mem_of_mem_tail hx)
      · exact inv.queue_used c' x (by simpa only [Function.update_of_ne hne] using hx)

theorem Inv.preserve_order_used {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : ∀ b ∈ s'.order, b ∈ s'.used := by
  cases step with
  | @create s parent b is_fresh =>
      exact fun x hx => Finset.mem_insert_of_mem (inv.order_used x hx)
  | @exchange s b c is_used is_next is_new chained => exact inv.order_used
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact inv.order_used x hx'
      · rw [List.mem_singleton.mp hx']; exact is_used
  | @run s b is_acquired not_active not_done heads => exact inv.order_used
  | @bodyDone s b is_active => exact inv.order_used
  | @release s b c is_done is_head => exact inv.order_used

theorem Inv.preserve_queue_taken {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ c, ∀ b ∈ s'.queues c, c ∈ (sortedClaims fclaims b).take (s'.progress b) := by
  cases step with
  | @create s parent b is_fresh =>
      intro c x hx
      rcases eq_or_ne x b with rfl | hne
      · exact absurd (inv.queue_used c x hx) is_fresh
      · simpa [Function.update_of_ne hne] using inv.queue_taken c x hx
  | @exchange s b c is_used is_next is_new chained =>
      intro c' x hx
      rcases eq_or_ne x b with rfl | hne
      · simp only [Function.update_self]
        rcases eq_or_ne c' c with rfl | hcne
        · rw [take_succ_eq_concat is_next]
          exact List.mem_append_right _ List.mem_cons_self
        · simp only [Function.update_of_ne hcne] at hx
          exact (List.take_prefix_take_left (Nat.le_succ _)).subset
            (inv.queue_taken c' x hx)
      · simp only [Function.update_of_ne hne]
        rcases eq_or_ne c' c with rfl | hcne
        · simp only [Function.update_self, List.mem_append] at hx
          rcases hx with hx | hx
          · exact inv.queue_taken c' x hx
          · exact absurd (List.mem_singleton.mp hx) hne
        · exact inv.queue_taken c' x (by simpa only [Function.update_of_ne hcne] using hx)
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.queue_taken
  | @run s b is_acquired not_active not_done heads => exact inv.queue_taken
  | @bodyDone s b is_active => exact inv.queue_taken
  | @release s b c is_done is_head =>
      intro c' x hx
      rcases eq_or_ne c' c with rfl | hne
      · simp only [Function.update_self] at hx
        exact inv.queue_taken c' x (List.mem_of_mem_tail hx)
      · exact inv.queue_taken c' x (by simpa only [Function.update_of_ne hne] using hx)

theorem Inv.preserve_queue_nodup {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : ∀ c, (s'.queues c).Nodup := by
  cases step with
  | @create s parent b is_fresh => exact inv.queue_nodup
  | @exchange s b c is_used is_next is_new chained =>
      intro c'
      rcases eq_or_ne c' c with rfl | hne
      · simp only [Function.update_self]
        exact (inv.queue_nodup c').append (List.nodup_singleton b)
          (List.disjoint_singleton.mpr is_new)
      · simp only [Function.update_of_ne hne]; exact inv.queue_nodup c'
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.queue_nodup
  | @run s b is_acquired not_active not_done heads => exact inv.queue_nodup
  | @bodyDone s b is_active => exact inv.queue_nodup
  | @release s b c is_done is_head =>
      intro c'
      rcases eq_or_ne c' c with rfl | hne
      · simp only [Function.update_self]; exact (inv.queue_nodup c').tail
      · simp only [Function.update_of_ne hne]; exact inv.queue_nodup c'

theorem Inv.preserve_order_nodup {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : s'.order.Nodup := by
  cases step with
  | @create s parent b is_fresh => exact inv.order_nodup
  | @exchange s b c is_used is_next is_new chained => exact inv.order_nodup
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.order_nodup.append (List.nodup_singleton b)
        (List.disjoint_singleton.mpr is_new)
  | @run s b is_acquired not_active not_done heads => exact inv.order_nodup
  | @bodyDone s b is_active => exact inv.order_nodup
  | @release s b c is_done is_head => exact inv.order_nodup

/-- A behaviour mid-acquire has not passed its linearization point. -/
theorem Inv.notMem_order_of_getElem? (inv : Inv fclaims s) {b : Id} {c : Cown}
    (is_next : (sortedClaims fclaims b)[s.progress b]? = some c) : b ∉ s.order := by
  intro hb
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp is_next
  exact absurd (inv.order_progress b hb) (Nat.ne_of_lt hlt)

theorem Inv.preserve_order_progress {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ b ∈ s'.order, s'.progress b = (sortedClaims fclaims b).length := by
  cases step with
  | @create s parent b is_fresh =>
      intro x hx
      have hne : x ≠ b := fun h => is_fresh (h ▸ inv.order_used x hx)
      simpa [Function.update_of_ne hne] using inv.order_progress x hx
  | @exchange s b c is_used is_next is_new chained =>
      intro x hx
      have hne : x ≠ b := fun h => inv.notMem_order_of_getElem? is_next (h ▸ hx)
      simpa [Function.update_of_ne hne] using inv.order_progress x hx
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact inv.order_progress x hx'
      · rw [List.mem_singleton.mp hx']; exact is_full
  | @run s b is_acquired not_active not_done heads => exact inv.order_progress
  | @bodyDone s b is_active => exact inv.order_progress
  | @release s b c is_done is_head => exact inv.order_progress

theorem Inv.preserve_queue_linearizes {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ c, ∀ b ∈ s'.order, b ∈ s'.queues c →
      ∀ x ∈ ahead (s'.queues c) b, Precedes s'.order x b := by
  cases step with
  | @create s parent b is_fresh => exact inv.queue_linearizes
  | @exchange s b c is_used is_next is_new chained =>
      intro c' y hy hyq x hx
      have hne : y ≠ b := fun h => inv.notMem_order_of_getElem? is_next (h ▸ hy)
      rcases eq_or_ne c' c with rfl | hcne
      · simp only [Function.update_self] at hyq hx
        have hyq' : y ∈ s.queues c' :=
          (List.mem_append.mp hyq).resolve_right fun h =>
            hne (List.mem_singleton.mp h)
        rw [ahead_append_of_mem hyq'] at hx
        exact inv.queue_linearizes c' y hy hyq' x hx
      · simp only [Function.update_of_ne hcne] at hyq hx
        exact inv.queue_linearizes c' y hy hyq x hx
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      intro c y hy hyq x hx
      rcases List.mem_append.mp hy with hy' | hy'
      · exact (inv.queue_linearizes c y hy' hyq x hx).trans (List.sublist_append_left _ _)
      · obtain rfl := List.mem_singleton.mp hy'
        have hxo : x ∈ s.order := inv.ahead_subset_order_of_mem chained hyq x hx
        exact List.Sublist.append (List.singleton_sublist.mpr hxo)
          (List.Sublist.refl [y])
  | @run s b is_acquired not_active not_done heads => exact inv.queue_linearizes
  | @bodyDone s b is_active => exact inv.queue_linearizes
  | @release s b c is_done is_head =>
      intro c' y hy hyq x hx
      rcases eq_or_ne c' c with rfl | hcne
      · simp only [Function.update_self] at hyq hx
        obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp is_head
        rw [ht] at hyq hx ⊢
        have hne : y ≠ b := fun h =>
          (List.nodup_cons.mp (ht ▸ inv.queue_nodup c')).1 (h ▸ hyq)
        refine inv.queue_linearizes c' y hy (ht ▸ List.mem_cons_of_mem b hyq) x ?_
        rw [ht, ahead_cons_of_ne (fun h => hne h.symm)]
        exact List.mem_cons_of_mem b hx
      · simp only [Function.update_of_ne hcne] at hyq hx
        exact inv.queue_linearizes c' y hy hyq x hx

theorem Inv.preserve_settled {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ b, ∀ c ∈ ((sortedClaims fclaims b).take (s'.progress b)).dropLast,
      b ∈ s'.queues c → ∀ x ∈ ahead (s'.queues c) b, x ∈ s'.order := by
  cases step with
  | @create s parent b is_fresh =>
      intro y c hc hyq
      rcases eq_or_ne y b with rfl | hne
      · exact absurd (inv.queue_used c y hyq) is_fresh
      · simp only [Function.update_of_ne hne] at hc
        exact inv.settled y c hc hyq
  | @exchange s b c is_used is_next is_new chained =>
      intro y c' hc' hyq x hx
      rcases eq_or_ne y b with rfl | hne
      · simp only [Function.update_self, take_succ_eq_concat is_next,
          List.dropLast_concat] at hc'
        have hcne : c' ≠ c := fun h =>
          notMem_take_of_getElem? (sortedClaims_nodup fclaims y) is_next (h ▸ hc')
        simp only [Function.update_of_ne hcne] at hyq hx
        exact inv.ahead_subset_order_of_mem chained hyq x hx
      · simp only [Function.update_of_ne hne] at hc'
        rcases eq_or_ne c' c with rfl | hcne
        · simp only [Function.update_self] at hyq hx
          have hyq' : y ∈ s.queues c' :=
            (List.mem_append.mp hyq).resolve_right fun h =>
              hne (List.mem_singleton.mp h)
          rw [ahead_append_of_mem hyq'] at hx
          exact inv.settled y c' hc' hyq' x hx
        · simp only [Function.update_of_ne hcne] at hyq hx
          exact inv.settled y c' hc' hyq x hx
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      intro y c hc hyq x hx
      exact List.mem_append_left _ (inv.settled y c hc hyq x hx)
  | @run s b is_acquired not_active not_done heads => exact inv.settled
  | @bodyDone s b is_active => exact inv.settled
  | @release s b c is_done is_head =>
      intro y c' hc' hyq x hx
      rcases eq_or_ne c' c with rfl | hcne
      · simp only [Function.update_self] at hyq hx
        obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp is_head
        rw [ht] at hyq hx
        have hne : y ≠ b := fun h =>
          (List.nodup_cons.mp (ht ▸ inv.queue_nodup c')).1 (h ▸ hyq)
        refine inv.settled y c' hc' (ht ▸ List.mem_cons_of_mem b hyq) x ?_
        rw [ht, ahead_cons_of_ne (fun h => hne h.symm)]
        exact List.mem_cons_of_mem b hx
      · simp only [Function.update_of_ne hcne] at hyq hx
        exact inv.settled y c' hc' hyq x hx

theorem Inv.preserve_active_done_disjoint {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : ∀ b ∈ s'.active, b ∉ s'.done := by
  cases step with
  | @create s parent b is_fresh => exact inv.active_done_disjoint
  | @exchange s b c is_used is_next is_new chained =>
      exact inv.active_done_disjoint
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.active_done_disjoint
  | @run s b is_acquired not_active not_done heads =>
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact not_done
      · exact inv.active_done_disjoint x hx'
  | @bodyDone s b is_active =>
      intro x hx hx'
      rcases Set.mem_insert_iff.mp hx' with rfl | hx''
      · exact hx.2 rfl
      · exact inv.active_done_disjoint x hx.1 hx''
  | @release s b c is_done is_head => exact inv.active_done_disjoint

theorem Inv.preserve_active_order {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : ∀ b ∈ s'.active, b ∈ s'.order := by
  cases step with
  | @create s parent b is_fresh => exact inv.active_order
  | @exchange s b c is_used is_next is_new chained => exact inv.active_order
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact fun x hx => List.mem_append_left _ (inv.active_order x hx)
  | @run s b is_acquired not_active not_done heads =>
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact is_acquired
      · exact inv.active_order x hx'
  | @bodyDone s b is_active => exact fun x hx => inv.active_order x hx.1
  | @release s b c is_done is_head => exact inv.active_order

theorem Inv.preserve_done_order {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : ∀ b ∈ s'.done, b ∈ s'.order := by
  cases step with
  | @create s parent b is_fresh => exact inv.done_order
  | @exchange s b c is_used is_next is_new chained => exact inv.done_order
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact fun x hx => List.mem_append_left _ (inv.done_order x hx)
  | @run s b is_acquired not_active not_done heads => exact inv.done_order
  | @bodyDone s b is_active =>
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact inv.active_order x is_active
      · exact inv.done_order x hx'
  | @release s b c is_done is_head => exact inv.done_order

theorem Inv.preserve_active_heads {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ b ∈ s'.active, ∀ c ∈ fclaims b, (s'.queues c).head? = some b := by
  cases step with
  | @create s parent b is_fresh => exact inv.active_heads
  | @exchange s b c is_used is_next is_new chained =>
      intro x hx c' hc'
      rcases eq_or_ne c' c with rfl | hcne
      · simp only [Function.update_self, List.head?_append, inv.active_heads x hx c' hc']
        rfl
      · simp only [Function.update_of_ne hcne]; exact inv.active_heads x hx c' hc'
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.active_heads
  | @run s b is_acquired not_active not_done heads =>
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact heads
      · exact inv.active_heads x hx'
  | @bodyDone s b is_active => exact fun x hx => inv.active_heads x hx.1
  | @release s b c is_done is_head =>
      intro x hx c' hc'
      have hxb : x ≠ b := fun h =>
        inv.active_done_disjoint x hx (h ▸ is_done)
      have hcne : c' ≠ c := by
        intro h
        exact hxb (Option.some_injective _
          ((h ▸ inv.active_heads x hx c' hc').symm.trans is_head))
      simp only [Function.update_of_ne hcne]; exact inv.active_heads x hx c' hc'

theorem Inv.preserve_done_heads {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') :
    ∀ b ∈ s'.done, ∀ c, b ∈ s'.queues c → (s'.queues c).head? = some b := by
  cases step with
  | @create s parent b is_fresh => exact inv.done_heads
  | @exchange s b c is_used is_next is_new chained =>
      intro x hx c' hxq
      have hxb : x ≠ b := fun h =>
        inv.notMem_order_of_getElem? is_next (h ▸ inv.done_order x hx)
      rcases eq_or_ne c' c with rfl | hcne
      · simp only [Function.update_self] at hxq ⊢
        have hxq' : x ∈ s.queues c' :=
          (List.mem_append.mp hxq).resolve_right fun h =>
            hxb (List.mem_singleton.mp h)
        rw [List.head?_append, inv.done_heads x hx c' hxq']
        rfl
      · simp only [Function.update_of_ne hcne] at hxq ⊢
        exact inv.done_heads x hx c' hxq
  | @acquireDone s parent b is_used is_parent is_full is_new chained =>
      exact inv.done_heads
  | @run s b is_acquired not_active not_done heads => exact inv.done_heads
  | @bodyDone s b is_active =>
      intro x hx c hxq
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · exact inv.active_heads x is_active c (inv.queue_mem_claims c hxq)
      · exact inv.done_heads x hx' c hxq
  | @release s b c is_done is_head =>
      intro x hx c' hxq
      rcases eq_or_ne c' c with rfl | hcne
      · simp only [Function.update_self] at hxq ⊢
        obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp is_head
        rw [ht] at hxq ⊢
        have hxb : x ≠ b := fun h =>
          (List.nodup_cons.mp (ht ▸ inv.queue_nodup c')).1 (h ▸ hxq)
        exact absurd (Option.some_injective _
          ((inv.done_heads x hx c' (ht ▸ List.mem_cons_of_mem b hxq)).symm.trans
            (by rw [ht]; rfl))) hxb
      · simp only [Function.update_of_ne hcne] at hxq ⊢
        exact inv.done_heads x hx c' hxq

/-- Every protocol step preserves the invariant. -/
theorem Inv.preserve {e : Event Cown Id} (inv : Inv fclaims s)
    (step : Step fclaims e s s') : Inv fclaims s' where
  progress_le := inv.preserve_progress_le step
  progress_used := inv.preserve_progress_used step
  queue_used := inv.preserve_queue_used step
  order_used := inv.preserve_order_used step
  queue_taken := inv.preserve_queue_taken step
  queue_nodup := inv.preserve_queue_nodup step
  order_nodup := inv.preserve_order_nodup step
  order_progress := inv.preserve_order_progress step
  queue_linearizes := inv.preserve_queue_linearizes step
  settled := inv.preserve_settled step
  active_done_disjoint := inv.preserve_active_done_disjoint step
  active_order := inv.preserve_active_order step
  done_order := inv.preserve_done_order step
  active_heads := inv.preserve_active_heads step
  done_heads := inv.preserve_done_heads step

theorem reachable_inv {initial : State Cown Id} (inv : Inv fclaims initial)
    (reach : Reachable fclaims initial s) : Inv fclaims s := by
  induction reach with
  | refl => exact inv
  | tail _ step ih =>
      obtain ⟨e, hstep⟩ := step
      exact ih.preserve hstep

/-! ## The bridge facts -/

/-- Mutual exclusion: two running behaviours never share a cown.  Every
running behaviour heads each queue it claimed, and a queue has one head.  This
is the protocol-side form of the kernel's `Safe`. -/
theorem Inv.eq_of_active_of_mem_claims (inv : Inv fclaims s) {b b' : Id} {c : Cown}
    (hb : b ∈ s.active) (hb' : b' ∈ s.active)
    (hbc : c ∈ fclaims b) (hb'c : c ∈ fclaims b') : b = b' :=
  Option.some_injective _
    ((inv.active_heads b hb c hbc).symm.trans (inv.active_heads b' hb' c hb'c))


/-- Queues refine the ghost completion order: whenever `x` sits before `b` in
some cown's queue and `b` has passed its acquire linearization point, `x`
precedes `b` in `order` too.  This is what a refinement of this machine by the
scheduler kernel consumes. -/
theorem Inv.queue_order_refines_order (inv : Inv fclaims s) (c : Cown) {x b : Id}
    (h_queue : Precedes (s.queues c) x b) (h_acquired : b ∈ s.order) :
    Precedes s.order x b :=
  inv.queue_linearizes c b h_acquired
    (h_queue.subset (List.mem_cons_of_mem _ List.mem_cons_self)) x
    (mem_ahead_of_precedes (inv.queue_nodup c) h_queue)

end Protocol

end Boc
