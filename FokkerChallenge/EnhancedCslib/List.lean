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
