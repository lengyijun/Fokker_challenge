import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem foldl_union_replicate_empty {fs : Finset String} (n : ℕ) :
    List.foldl (· ∪ ·) fs (List.replicate n ∅) = fs := by
  induction n generalizing fs with
  | zero => grind
  | succ n ih =>
    simp [List.replicate_succ]
    rw [ih]
    grind

@[scoped grind]
lemma union_foldl {l : List _} {fs : Finset String}:
  fs ⊆ l.foldl Union.union fs := by
  induction l generalizing fs with grind

/-- Any member of `xs` is at most `xs.max?.getD d`, for any default `d`. -/
theorem List.mem_le_max?_getD {α : Type*} [Max α] [LE α]
    [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {xs : List α} {x d : α} (hx : x ∈ xs) : x ≤ xs.max?.getD d := by
  rcases hopt : xs.max? with _ | m
  · simp [List.max?_eq_none_iff.mp hopt] at hx
  · simpa [hopt] using (List.max?_eq_some_iff.mp hopt).2 x hx
