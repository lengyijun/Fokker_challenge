import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
inductive ClosedUnderApp (P: Term String -> Prop): Term String -> Prop where
  | base {a}: P a -> ClosedUnderApp P a
  | app {a b}: ClosedUnderApp P a -> ClosedUnderApp P b -> ClosedUnderApp P (.app a b)

theorem closedunderapp_multiapp {Q} {M : Term String}
  (h2 : ClosedUnderApp Q M) :
  ∃ (l: List (Term String)) (f : Term String), M = l.foldl Term.app f /\ Q f /\ ∀ x ∈ l, ClosedUnderApp Q x := by
  induction h2 with
  | base _ => rename_i M _
              exists []
              exists M
              grind
  | app _ _ iha ihb =>
      rename_i a b _ _
      obtain ⟨la, fa, iha⟩ := iha
      obtain ⟨lb, fb, ihb⟩ := ihb
      exists (la ++ [b])
      exists fa
      grind

theorem closedunderapp_multiapp_cons {l : List (Term String)} {Q} {f: Term String}:
  (∀ x ∈ l, ClosedUnderApp Q x) ->
  ClosedUnderApp Q f ->
  ClosedUnderApp Q (l.foldl Term.app f) := by
  induction l generalizing f with
  | nil => grind
  | cons head tail ih =>
    intros _ _
    simp
    apply ih <;> grind

@[scoped grind]
theorem closedunderapp_lc {Q} {M : Term String}
  (h : ∀ x, Q x -> x.LC)
  (h2 : ClosedUnderApp Q M) :
  M.LC := by
  induction h2 with grind
