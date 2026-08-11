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
import FokkerChallenge.EnhancedCslib.HeadSN
import FokkerChallenge.EnhancedCslib.EtaSpineOpenFv
import FokkerChallenge.EnhancedCslib.HeadNFSpineBeta
import FokkerChallenge.TwoVarsAreNotEnough.Basic
import FokkerChallenge.TwoVarsAreNotEnough.Head2
import FokkerChallenge.TwoVarsAreNotEnough.Unroll
import FokkerChallenge.TwoVarsAreNotEnough.Q
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

theorem final {n M}
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
  obtain ⟨beta_nf, beta_steps, h_beta_nf⟩ := h_beta_nf
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta steps (FullBetaEta.from_beta _ _ beta_steps)
  have := Relation.Normal.reflTransGen_eq h_betaeta_nf hz1
  subst Z
  have eta_steps : beta_nf ↠ηᶠ List.foldl app (fvar "x") [(fvar "y").app (H n)] := beta_eta_star_of_beta_normal h_beta_nf hz2
  have beta_nf_lc : beta_nf.LC := by cases FullBeta.steps_lc_or_rfl beta_steps <;> grind
  obtain ⟨i, E, l, beta_nf_eq, _, he, _, _, _, _⟩ := betaNF_etaStar_shape_len_one_openDown_fv beta_nf_lc h_beta_nf eta_steps
  have h1 := steps_multiApp_l (Ns := List.replicate i (fvar "y")) beta_steps (by grind)
  rw [beta_nf_eq] at h1
  obtain h2 := redex_n_apps_n_abs_of_apps "y" (List.foldl app (fvar "x") (E :: l)) i (by grind)
  rw [openDown_multiapp, openDown_fvar] at h2
  -- have : (abs^[i] (List.foldl app (fvar "x") l)).LC := by
  --   rw [beta_nf_eq] at beta_nf_lc
  --   rw [<- lcAt_iff_LC, absn_lcat, app_lcat] at *
  --   grind
  have : M.LC := closedunderapp_lc (by grind) hm
  have recursive_app_lc : (List.foldl app (fvar "x") (List.map (openDown i (fvar "y")) (E :: l))).LC := by
    cases FullBeta.steps_lc_or_rfl (h1.trans h2) with
    | inl h => grind
    | inr h =>  rw [<- h, multiApp_lc]
                grind
  have hnf : HasHNF _ := ⟨_, h1.trans h2, .neutral ((multiapp_headneutral (by grind)))⟩
  rw [hasHNF_iff_headStepStar_headNF] at hnf
  obtain ⟨P, hsteps, hnf⟩ := hnf
  obtain ⟨Z, hz1, hz2⟩ := confluent_fullBeta (h1.trans h2) (HeadStepStar.toFullBetaStar hsteps)
  obtain ⟨l', _, hl'⟩ := beta_steps_preserve_fvar_apps hz1
  subst Z
  obtain ⟨l'', _, hl''⟩:= steps_headnf_preserve_multiapp hnf hz2
  subst P
  have hm2 : ClosedUnderApp fvar_or_combinator M := closedunderapp_derive (by grind) hm
  have h2steps := HeadReduction2.headneutral_exists (closedunderapp_multiapp_cons (by grind) (by grind)) (HeadNF.of_not_isAbs hnf (by cases l'' using List.reverseRecOn <;> grind)) hsteps
  have heq : (List.foldl app ((fvar "x").app ((fvar "y").app (H n))) (List.replicate i (fvar "y"))) =
  (List.foldl app (fvar "x") ( ((fvar "y").app (H n)) :: List.replicate i (fvar "y"))) := by grind
  have g := steps_multiApp_l_union (Ns := List.replicate i (fvar "y")) steps (by grind)
  rw [heq] at g
  obtain ⟨_, hq, _⟩ := steps_closedUnderApp_unroll_q hm2 ⟨beta_eta_spline_contain_x g, closedunderapp_multiapp_cons (by grind) (by grind), closedunderapp_multiapp_cons (by grind) (by grind)⟩ _ h2steps
  cases hl' with | cons hl' _ =>
  cases hl'' with | cons hl'' _ =>
  rw [openDown_lc (by assumption)] at hl'
  obtain ⟨Z, hz1, hz2⟩ := confluent_beta_eta (FullBetaEta.from_eta _ _ he) (FullBetaEta.from_beta _ _ hl')
  have := Relation.Normal.reflTransGen_eq (by rw [exists_beta_normal_fvar_app_of_beta_eta]; apply normal_H) hz1
  subst_vars
  apply FullBetaEta.steps_fv at hz2
  apply FullBeta.steps_fv at hl''
  simp at hz2
  have hq := closedUnderApp_q_of_foldl_app "y" (by grind) (by grind [closedunderapp_fv (by grind) hm]) hq
  cases hq with | base hq =>
  rcases hq with _|hq|_ <;> try grind
  obtain ⟨l, hx, _⟩:= unroll_2_vars_are_enough_foldl (by grind) hq
  -- h2steps
  sorry
