
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaConfluence
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.FlipApp
import FokkerChallenge.EnhancedCslib.LeftMost
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
-- import FokkerChallenge.EnhancedCslib.Spine
import FokkerChallenge.EnhancedCslib.ReflTransGenWithSteps
import FokkerChallenge.EnhancedCslib.HeadRed
import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.TwoVarsAreNotEnough.Head2
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
def Q (mx a: Term String) : Prop := a = (fvar "y") \/
                                    unroll mx a \/
                                    (a.abs_two_vars_are_enough /\ a.depth < mx.depth)

theorem Q_lc {M}
  (hm : ClosedUnderApp fvar_or_combinator M):
  ∀ t, Q (M.app (fvar "x")) t -> t.LC := by
  intros x hx
  rcases hx with hx|hx|hx
  . grind
  . apply unroll.LC hx
    apply LC.app (closedunderapp_lc (by grind) hm) (LC.fvar _)
  . grind

theorem closed_under_app_Q {M t N1 N0}
  (g : two_vars_are_enough t)
  (ht :t.depth < M.depth)
  (h0: ClosedUnderApp (Q M) N0)
  (h1: ClosedUnderApp (Q M) N1)
  (hlc: N1.LC) :
  ClosedUnderApp (Q M) (t⟦1 ↝ N1⟧⟦0 ↝ N0⟧) := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with | h n ih => cases t with
  | fvar => grind
  | bvar a => have h : a = 0 \/ a = 1 := by grind
              cases h <;> subst_vars
              . grind
              . simp [openRec]
                rw [open_lc] <;> grind
  | app _ _ =>
    refine .app ?_ ?_ <;> apply ih
    any_goals rfl
    any_goals grind
    all_goals simp_all
  | abs t => cases t with
    | abs _ => grind
    | bvar _ => unfold two_vars_are_enough at g
                grind
    | fvar _ => unfold two_vars_are_enough at g
                grind
    | app _ _ =>  unfold two_vars_are_enough at g
                  grind

theorem closedUnderApp_unroll {M}
  (h_contain_x : contain_x ((M.app (fvar "x")).app (fvar "y")))
  (hm : ClosedUnderApp fvar_or_combinator M):
  ∀ N, (M.app (fvar "x")).app (fvar "y") ↠𝒽 N ->
       ClosedUnderApp (Q (M.app (fvar "x"))) N := by
  intros N g
  induction g with
  | refl => refine .app (.base ?_) (by grind)
            right
            left
            refine .refl
  | tail h1 h2 ih =>
    obtain ⟨l, f, h3, h4, h5⟩ := closedunderapp_multiapp ih
    rcases h4 with h4|h4|⟨h4, h6⟩
    . subst_vars
      exfalso
      apply head_fvar h2
    . subst_vars
      rcases foldl_multiapp_cases h2 with ⟨f', h2, _⟩|⟨a, b, l', f', _, _, h2⟩|⟨a, b, l', f', _, _, h2⟩
      . subst_vars
        refine closedunderapp_multiapp_cons (by grind) (.base ?_)
        right
        left
        exact .trans h4 (.single (.reflTrans (by grind)))
      . subst_vars
        apply closedunderapp_multiapp_cons (by grind)
        cases unroll_fvar_or_combinator (by grind) h4 with
        | base h => grind
        | app h _ => cases h with | base h => cases h with
        | inl h => cases h
        | inr h =>  simp at h5
                    obtain ⟨h5, _⟩ := h5
                    unfold abs_two_vars_are_enough at h
                    split at h <;> try grind
                    rename_i heq
                    cases heq
                    have h7 : (M.app (fvar "x")).Q a := by
                      right
                      left
                      refine .tail h4 (.throughAbsApp)
                    apply closed_under_app_Q h
                    . have := unroll.depth (by grind) h4
                      simp_all
                      grind
                    . grind
                    . grind
                    . apply Q_lc hm _ h7
      . exfalso
        subst_vars
        cases unroll_fvar_or_combinator (by grind) h4 with | base h3 => cases h3 with
        | inl => grind
        | inr =>  obtain ⟨l, h, _⟩ := unroll_2_vars_are_enough_foldl (by grind) h4
                  have h := FullBeta.redex_app_l_cong h (LC.fvar "y")
                  have h1 := h_contain_x _ h
                  unfold fv at h1
                  rw [flip_app_fv] at h1
                  have h5 : ∀ x ∈ l, x.fv = ∅ := by grind
                  rw [<- List.map_eq_replicate_iff] at h5
                  rw [h5] at h1
                  have h5 : f'.abs.abs.fv = ∅ := by grind
                  rw [h5, foldl_union_replicate_empty] at h1
                  simp [fv] at h1
    . unfold abs_two_vars_are_enough at h4
      split at h4 <;> try grind
      subst_vars
      rcases foldl_multiapp_cases h2 with ⟨f', h2, _⟩|⟨a, b, l', f', _, h2, _⟩|⟨a, b, l', f', _, h3, h2⟩
      . cases h2
      . cases h2
      . cases h3
        subst_vars
        apply closedunderapp_multiapp_cons (by grind)
        apply closed_under_app_Q (by assumption) (by grind) (by grind) (by grind)
        exact closedunderapp_lc (Q_lc hm) (h5 a (by grind))
