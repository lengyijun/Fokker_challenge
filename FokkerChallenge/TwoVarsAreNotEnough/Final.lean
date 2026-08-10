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
import FokkerChallenge.EnhancedCslib.EtaToSpine
import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.TwoVarsAreNotEnough.Head2
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem closedUnderApp_unroll_z {n M}
  (h_depth : M.depth <= n)
  (hm : ClosedUnderApp (fun t => t.abs_two_vars_are_enough) M)
  (steps : ((M.app (fvar "x")).app (fvar "y")) ↠βηᶠ (fvar "x").app ((fvar "y").app (H n))) : False := by
  induction n using Nat.strong_induction_on generalizing M with | h n ih =>
  have h : Relation.Normalizable FullBetaEta ((M.app (fvar "x")).app (fvar "y")) := by
    refine ⟨_, steps, ?_⟩
    rw [exists_beta_normal_fvar_app_of_beta_eta, exists_beta_normal_fvar_app_of_beta_eta]
    apply normal_H
  rw [<- hasBetaEtaNF_iff_hasBetaNF] at h
  obtain ⟨beta_nf, h, h_beta_nf⟩ := h
  have : beta_nf ↠ηᶠ List.foldl app (fvar "x") [(fvar "y").app (H n)] := by sorry
  have := betaNF_etaStar_absN_spine beta_nf "x" [(fvar "y").app (H n)] h_beta_nf ?_
  all_goals sorry
