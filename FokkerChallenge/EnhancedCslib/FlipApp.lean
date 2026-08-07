import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

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
