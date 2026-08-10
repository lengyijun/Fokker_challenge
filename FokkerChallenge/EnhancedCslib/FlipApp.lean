import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta

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

lemma multiapp_fv {M} {Ns : List (Term String)}:
  (Ns.foldl app M).fv = (Ns.map fv).foldl Union.union M.fv := by
    induction Ns generalizing M with
    | nil => grind
    | cons head tail ih =>
      simp
      specialize @ih (M.app head)
      grind

lemma flip_app_lc {M} {l : List (Term String)}:
  (l.foldl (flip app) M).LC <-> M.LC /\ ∀ x ∈ l, x.LC := by
  induction l generalizing M with
  | nil => grind
  | cons head tail ih =>  simp [flip]
                          specialize @ih (head.app M)
                          rw [ih]
                          constructor
                          . intros h
                            cases h with | intro h _ =>
                            cases h
                            grind
                          . grind

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

lemma listfullBeta_exists (P : Term String -> Prop) (Ns : List (Term String))
  (h_lc : ∀ M ∈ Ns, LC M)
  (h : ∀ t ∈ Ns, ∃ t', t ↠βᶠ t' /\ P t') :
  ∃ Ns', Ns ↠lβᶠ Ns' /\ ∀ t ∈ Ns', P t := by
  induction Ns with
  | nil =>  use []
            grind
  | cons head tail ih =>
  obtain ⟨Ns', h1, _⟩ := ih (by grind) (by grind)
  simp at h
  obtain ⟨⟨t', h, _⟩, _⟩ := h
  exact ⟨t' :: Ns', .trans (listFullBeta_cons_r h1 (by grind)) (listFullBeta_cons_l h (multiApp_steps_lc h1 (by grind))), by grind⟩

lemma multiapp_openrec {M N i} {l : List (Term String)}:
  ∃ l' : List _, (l.foldl app M)⟦i ↝ N⟧ = l'.foldl app (M⟦i ↝ N⟧) := by
  induction l generalizing M with
  | nil =>  use []
            grind
  | cons head tail ih =>
  obtain ⟨l, h⟩ := @ih (M.app head)
  use (head⟦i ↝ N⟧ :: l)
  grind

theorem iterate_app {M M' Z : Term String} (n) (h: M ↠βᶠ M') (z_lc :Z.LC):
  (fun a => a.app Z)^[n] M ↠βᶠ (fun a => a.app Z)^[n] M' := by
  induction n generalizing M M' with simp
  | zero => grind
  | succ n ih => exact ih (FullBeta.redex_app_l_cong h z_lc)

theorem abs_openrec {i n} {N M : Term String} :
  (abs^[n] M)⟦i ↝ N⟧ = abs^[n] (M⟦n+i ↝ N⟧) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih => simp; grind

theorem redex_n_apps_n_abs_of_apps (n x y) (l : List (Term String))
  (h_lc : (abs^[n] (l.foldl app (fvar x))).LC) :
  ∃ l' : List _, (fun a => a.app (fvar y))^[n] (abs^[n] (l.foldl app (fvar x))) ↠βᶠ l'.foldl app (fvar x) := by
  induction n generalizing l with
  | zero => simp; grind
  | succ n ih =>
  nth_rewrite 2 [add_comm]
  rw [Function.iterate_add abs]
  simp
  obtain ⟨l', h⟩ := @multiapp_openrec (fvar x) (fvar y) n l
  rw [openRec_fvar] at h
  specialize @ih l' ?_
  . rw [<- h]
    have heq : n = n + 0 := by grind
    nth_rewrite 2 [heq]
    rw [<- abs_openrec]
    rw [<- lcAt_iff_LC] at *
    rw [lcAt_openRec_fvar_iff_lcAt]
    rw [add_comm, Function.iterate_add abs] at h_lc
    simp at h_lc
    grind
  . obtain ⟨l'', ih⟩ := ih
    refine ⟨l'', .trans (iterate_app _ (.head (.base (.beta ?_ (by grind))) ?_) (by grind)) ih⟩
    . rw [add_comm, Function.iterate_add abs] at h_lc
      simp at h_lc
      grind
    . unfold open'
      rw [abs_openrec]
      simp
      rw [h]
