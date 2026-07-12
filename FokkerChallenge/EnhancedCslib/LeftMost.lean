import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem leftmost_multiapp (f a: Term String) (l) : f.abs.LC -> a.LC ->
  (a :: l).foldl Term.app f.abs ⭢ℓ l.foldl Term.app (f^a) := by
  induction l using List.reverseRecOn generalizing f a with
  | nil => apply BetaAt.outer
  | append_singleton l a _ => intros _ _
                              simp
                              apply BetaAt.appNoAbsL
                              grind
                              intros h
                              generalize heq : (List.foldl app (f.abs.app a) l) = Q
                              rw [heq] at h
                              cases h
                              induction l using List.reverseRecOn with grind

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
