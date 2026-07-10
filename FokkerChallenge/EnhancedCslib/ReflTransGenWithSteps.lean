import Mathlib.Logic.Relation

inductive ReflTransGenWithSteps (r : α → α → Prop) : Nat → α → α → Prop
  | refl (a : α) : ReflTransGenWithSteps r 0 a a
  | step {n : Nat} {a b c : α}
      (h : ReflTransGenWithSteps r n a b) (h' : r b c) :
      ReflTransGenWithSteps r (n + 1) a c

theorem reflTransGenWithSteps_to_ReflTransGen {r : α → α → Prop} {n a b} :
    ReflTransGenWithSteps r n a b → Relation.ReflTransGen r a b := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step _ h1 h2 => exact Relation.ReflTransGen.tail h2 h1

/-- **Reverse** of `reflTransGenWithSteps_to_ReflTransGen`:
    Every `ReflTransGen` chain can be witnessed with an explicit step count. -/
theorem exists_ReflTransGenWithSteps {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ n, ReflTransGenWithSteps r n a b := by
  induction h with
  | refl =>
      exact ⟨0, ReflTransGenWithSteps.refl a⟩
  | tail h' hr ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, ReflTransGenWithSteps.step hn hr⟩
