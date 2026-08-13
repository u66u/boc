import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation

/-!
# Forward simulation for labeled transition systems

Generic machinery relating two labeled step relations along a state abstraction
-/

namespace Boc

variable {State Event : Type*}
variable {StateA EventA StateB EventB StateC EventC : Type*}

/-- some event fires. -/
abbrev StepAny (Step : Event → State → State → Prop) (s s' : State) : Prop :=
  ∃ e, Step e s s'

/-- Forward simulation of `StepA` by `StepB` along the state abstraction `f`:
on states satisfying `Inv`, a concrete step whose event abstracts to `some e'`
is matched by an abstract `e'`-step, and one whose event abstracts to `none`
stutters. -/
def Simulation (StepA : EventA → StateA → StateA → Prop)
    (StepB : EventB → StateB → StateB → Prop)
    (f : StateA → StateB) (eventAbs : EventA → Option EventB)
    (Inv : StateA → Prop) : Prop :=
  ∀ e a a', Inv a → StepA e a a' →
    match eventAbs e with
    | some e' => StepB e' (f a) (f a')
    | none => f a' = f a

/-- An invariant preserved by every labeled step holds in every reachable
state. -/
theorem reachable_invariant
    {Step : Event → State → State → Prop} {Inv : State → Prop}
    (preserves : ∀ e s s', Inv s → Step e s s' → Inv s')
    {s s' : State} (inv : Inv s)
    (reach : Relation.ReflTransGen (StepAny Step) s s') :
    Inv s' := by
  induction reach with
  | refl => exact inv
  | tail _ step ih =>
      obtain ⟨e, hstep⟩ := step
      exact preserves e _ _ ih hstep

/--  any simulation whose invariant is preserved lifts
reflexive-transitive reachability along `f`, `none`-labeled steps contributing
stutters. -/
theorem Simulation.liftOption
    {StepA : EventA → StateA → StateA → Prop}
    {StepB : EventB → StateB → StateB → Prop}
    {f : StateA → StateB} {eventAbs : EventA → Option EventB}
    {Inv : StateA → Prop}
    (sim : Simulation StepA StepB f eventAbs Inv)
    (preserves : ∀ e a a', Inv a → StepA e a a' → Inv a')
    {a a' : StateA} (inv : Inv a)
    (reach : Relation.ReflTransGen (StepAny StepA) a a') :
    Relation.ReflTransGen (StepAny StepB) (f a) (f a') := by
  induction reach with
  | refl => exact .refl
  | @tail b c hab step ih =>
      obtain ⟨e, hstep⟩ := step
      have hsim := sim e b c (reachable_invariant preserves inv hab) hstep
      cases heq : eventAbs e with
      | some e' =>
          rw [heq] at hsim
          exact ih.tail ⟨e', hsim⟩
      | none =>
          rw [heq] at hsim
          exact (show f c = f b from hsim) ▸ ih

/-- Simulations compose: state abstractions by function composition, event
abstractions by `Option.bind`.  The lower invariant must entail the upper one
across `f`. -/
theorem Simulation.comp
    {StepA : EventA → StateA → StateA → Prop}
    {StepB : EventB → StateB → StateB → Prop}
    {StepC : EventC → StateC → StateC → Prop}
    {f : StateA → StateB} {g : StateB → StateC}
    {eventAbsAB : EventA → Option EventB}
    {eventAbsBC : EventB → Option EventC}
    {InvA : StateA → Prop} {InvB : StateB → Prop}
    (simAB : Simulation StepA StepB f eventAbsAB InvA)
    (simBC : Simulation StepB StepC g eventAbsBC InvB)
    (compat : ∀ a, InvA a → InvB (f a)) :
    Simulation StepA StepC (g ∘ f)
      (fun e => (eventAbsAB e).bind eventAbsBC) InvA := by
  intro e a a' inva step
  have hAB := simAB e a a' inva step
  dsimp only
  cases heq : eventAbsAB e with
  | some eb =>
      rw [heq] at hAB
      exact simBC eb (f a) (f a') (compat a inva) hAB
  | none =>
      rw [heq] at hAB
      exact congrArg g hAB

/-- Splitting a filtered list at the unique element where two predicates flip
from `true` to `false`: where `p` and `q` agree except at `b ∈ l`, the
`p`-filtration is the `q`-filtration with `b` inserted. -/
theorem filter_split_of_flip {α : Type*} {l : List α} {p q : α → Bool} {b : α}
    (hb : b ∈ l) (hnd : l.Nodup)
    (hagree : ∀ x ∈ l, x ≠ b → p x = q x) (hpb : p b = true) (hqb : q b = false) :
    ∃ u v, l.filter p = u ++ b :: v ∧ l.filter q = u ++ v := by
  induction l with
  | nil => exact absurd hb List.not_mem_nil
  | cons a l ih =>
      obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hb with rfl | hbl
      · refine ⟨[], l.filter q, ?_, ?_⟩
        · rw [List.filter_cons_of_pos hpb, List.nil_append,
            List.filter_congr fun x hx =>
              hagree x (List.mem_cons_of_mem _ hx) fun h => ha (h ▸ hx)]
        · rw [List.filter_cons_of_neg (ne_true_of_eq_false hqb), List.nil_append]
      · have hpq : p a = q a :=
          hagree a List.mem_cons_self fun h => ha (h ▸ hbl)
        obtain ⟨u, v, hp, hq⟩ := ih hbl hnd'
          fun x hx hxb => hagree x (List.mem_cons_of_mem _ hx) hxb
        cases hpa : p a with
        | true =>
            exact ⟨a :: u, v,
              by rw [List.filter_cons_of_pos hpa, hp, List.cons_append],
              by rw [List.filter_cons_of_pos (hpq ▸ hpa), hq, List.cons_append]⟩
        | false =>
            exact ⟨u, v,
              by rw [List.filter_cons_of_neg (ne_true_of_eq_false hpa), hp],
              by rw [List.filter_cons_of_neg
                (ne_true_of_eq_false (hpq ▸ hpa)), hq]⟩

end Boc
