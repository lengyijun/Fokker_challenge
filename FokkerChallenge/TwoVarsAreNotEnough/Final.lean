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
  have h_betaeta_nf : Relation.Normal FullBetaEta ((fvar "x").app ((fvar "y").app (H n))) := by
    rw [exists_beta_normal_fvar_app_of_beta_eta, exists_beta_normal_fvar_app_of_beta_eta]
    apply normal_H
  have h : Relation.Normalizable FullBetaEta ((M.app (fvar "x")).app (fvar "y")) := ⟨_, steps, h_betaeta_nf⟩
  have h_beta_nf := h
  rw [<- hasBetaEtaNF_iff_hasBetaNF] at h_beta_nf
  obtain ⟨beta_nf, h, h_beta_nf⟩ := h_beta_nf
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta steps (FullBetaEta.from_beta h)
  have := Relation.Normal.reflTransGen_eq h_betaeta_nf hz1
  subst Z
  have eta_steps : beta_nf ↠ηᶠ List.foldl app (fvar "x") [(fvar "y").app (H n)] := beta_eta_star_of_beta_normal h_beta_nf hz2
  obtain ⟨i, l, beta_nf_eq⟩ := betaNF_etaStar_absN_spine beta_nf "x" [(fvar "y").app (H n)] h_beta_nf eta_steps
  all_goals sorry
