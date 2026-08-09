import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

lemma step_flip_app_l {M M'} {Ns : List (Term String)} (steps : M ⭢βᶠ M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    Ns.foldl (flip app) M ⭢βᶠ Ns.foldl (flip app) M' := by
  induction Ns generalizing M M' with
  | nil => grind
  | cons head tail ih =>  simp [flip]
                          apply ih <;> grind

lemma steps_flip_app_l {M M'} {Ns : List (Term String)} (steps : M ↠βᶠ M') (lc_Ns : ∀ N ∈ Ns, LC N) :
    Ns.foldl (flip app) M ↠βᶠ Ns.foldl (flip app) M' := by
  induction steps <;> grind [step_flip_app_l]

lemma flip_app_fv {M} {Ns : List (Term String)}:
  (Ns.foldl (flip app) M).fv = (Ns.map fv).foldl Union.union M.fv := by
    induction Ns generalizing M with
    | nil => grind
    | cons head tail ih =>
      simp [flip]
      specialize @ih (head.app M)
      grind

lemma flip_app_lc {M} {l : List (Term String)}
  (hm : M.LC)
  (hl : ∀ x ∈ l, x.LC) :
  (l.foldl (flip app) M).LC := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  unfold flip
                          apply ih <;> grind

lemma flip_app_eq {x y} {l l': List (Term String)}:
  l.foldl (flip app) (fvar x) = l'.foldl (flip app) (fvar y) ->
  x = y := by
  induction l using List.reverseRecOn generalizing l' with
  | nil => cases l' using List.reverseRecOn <;> simp [flip]
  | append_singleton l a _ => cases l' using List.reverseRecOn with
    | nil => simp [flip]
    | append_singleton l a _ => simp [flip]; grind

lemma app_eq {x y} {l l': List (Term String)}:
  l.foldl app (fvar x) = l'.foldl app (fvar y) ->
  x = y := by
  induction l using List.reverseRecOn generalizing l' with
  | nil => cases l' using List.reverseRecOn <;> simp
  | append_singleton l a _ => cases l' using List.reverseRecOn with
    | nil => simp
    | append_singleton l a _ => simp; grind

lemma beta_step_preserve_fvar_apps {x M} {l: List (Term String)}
  (step : l.foldl app (fvar x) ⭢βᶠ M)  :
  ∃ l': List _, M = l'.foldl app (fvar x) := by
  induction l using List.reverseRecOn generalizing M with
  | nil =>  cases step with | base h => cases h
  | append_singleton l a ih =>
  simp at step
  cases step with
  | base h => exfalso
              generalize heq : (List.foldl app (fvar x) l) = M
              rw [heq] at h
              cases h
              cases l using List.reverseRecOn <;> grind
  | appL h ih =>
    rename_i N
    use (l ++ [N])
    grind
  | appR h g => obtain ⟨l', ih⟩ := ih g
                use (l' ++ [a])
                grind

lemma beta_steps_preserve_fvar_apps {x M} {l: List (Term String)}
  (steps : l.foldl app (fvar x) ↠βᶠ M)  :
  ∃ l': List _, M = l'.foldl app (fvar x) := by
  induction steps with grind [beta_step_preserve_fvar_apps]

lemma beta_normal_of_eta_to_fvar_apps {x M N} {l: List (Term String)}
  (hn : l.foldl app (fvar x) = N)
  (hM : Relation.Normal FullBeta M)
  (steps : M ↠ηᶠ N) :
  (∃ l': List _, M = l'.foldl app (fvar x)) \/
  (∃ l': List _, M = ((l'.foldl app (fvar x)).app (bvar 0)).abs) := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => grind
  | head h' h ih =>
    specialize ih (Etastar_normal (.single h') hM)
    cases h' with
    | appL _ _ => sorry
    | appR _ _ => sorry
    | base h' => cases h' with | eta h' =>
        rcases ih with _|⟨l, ih⟩
        . grind
        . subst_vars
          exfalso
          apply hM
          refine ⟨((List.foldl app (fvar x) l).app (bvar 0)).abs, Xi.abs ∅ fun x hx => .base ?_⟩
          convert Beta.beta h' (LC.fvar x)
          unfold open' openRec
          rw [open_lc _ _ _ h']
          grind
    | abs xs _ => rcases ih with ⟨l, ih⟩|⟨l, ih⟩
                  .  cases l using List.reverseRecOn with
                    | nil => simp at ih
                    | append_singleton l a _ => simp; grind
                  . cases ih
                    right
                    sorry
