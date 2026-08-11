import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import FokkerChallenge.EnhancedCslib.HeadSN
import FokkerChallenge.EnhancedCslib.EtaSpineOpenFv

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-!
# β-reduction of a head normal form to a variable-headed spine

If a head normal form `M` β-reduces (in any number of steps) to an application
spine `x N₁ … Nₖ` headed by a *free* variable, then `M` is already such a spine,
`M = x N'₁ … N'ₖ`, and the arguments β-reduce componentwise, `N'ᵢ ↠β Nᵢ`.

The main result is `steps_headnf_preserve_multiapp`.  Along the way we prove the
basic inversion lemmas for β-steps out of an application or an abstraction, and
the fact that β-reduction out of a spine can only take place inside the
arguments (`spine_fullBetaStar_inv`).
-/


universe u

open Term

variable {Var : Type u} [HasFresh Var]

/-! ## Inversion lemmas for a single β-step -/

/-- A β-step out of an application either contracts the top-level redex, or
takes place in the argument, or in the function. -/
theorem fullBeta_app_inv {A B N : Term Var} (h : FullBeta (app A B) N) :
    (∃ C, A = abs C ∧ N = C ^ B) ∨ (∃ B', N = app A B' ∧ FullBeta B B') ∨
      (∃ A', N = app A' B ∧ FullBeta A A') := by
  cases h with
  | base hb => cases hb with | beta _ _ => exact Or.inl ⟨_, rfl, rfl⟩
  | appL _ hs => exact Or.inr (Or.inl ⟨_, rfl, hs⟩)
  | appR _ hs => exact Or.inr (Or.inr ⟨_, rfl, hs⟩)

/-- A β-step out of an abstraction yields an abstraction. -/
theorem fullBeta_abs_inv {T N : Term Var} (h : FullBeta (abs T) N) :
    ∃ T', N = abs T' := by
  cases h with
  | base hb => cases hb
  | abs xs _ => exact ⟨_, rfl⟩

/-- Many β-steps out of an abstraction yield an abstraction. -/
theorem fullBetaStar_abs_inv {T N : Term Var} (h : (abs T) ↠βᶠ N) :
    ∃ T', N = abs T' := by
  induction h with
  | refl => exact ⟨T, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨T', rfl⟩ := ih
      exact fullBeta_abs_inv hstep

/-! ## Componentwise β-reduction of argument lists -/

theorem forall₂_betaStar_refl (l : List (Term Var)) :
    List.Forall₂ (Relation.ReflTransGen FullBeta) l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons Relation.ReflTransGen.refl ih

theorem forall₂_betaStar_trans {l₁ l₂ l₃ : List (Term Var)}
    (h₁ : List.Forall₂ (Relation.ReflTransGen FullBeta) l₁ l₂) (h₂ : List.Forall₂ (Relation.ReflTransGen FullBeta) l₂ l₃) :
    List.Forall₂ (Relation.ReflTransGen FullBeta) l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact List.Forall₂.nil
  | cons hab _ ih =>
      cases h₂ with
      | cons hbc hrest => exact List.Forall₂.cons (hab.trans hbc) (ih hrest)

theorem forall₂_betaStar_concat {l₁ l₂ : List (Term Var)} {a b : Term Var}
    (h : List.Forall₂ (Relation.ReflTransGen FullBeta) l₁ l₂) (hab : (Relation.ReflTransGen FullBeta) a b) :
    List.Forall₂ (Relation.ReflTransGen FullBeta) (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons hh _ ih => exact List.Forall₂.cons hh ih

/-! ## Spines are injective -/

/-- The head variable and the argument list of a spine are uniquely determined. -/
theorem spine_inj {x y : Var} {l₁ l₂ : List (Term Var)}
    (h : spine x l₁ = spine y l₂) : x = y ∧ l₁ = l₂ := by
  induction l₁ using List.reverseRecOn generalizing l₂ with
  | nil =>
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₀, b, rfl⟩
      · exact ⟨by cases h; rfl, rfl⟩
      · rw [List.concat_eq_append, spine_concat, spine_nil] at h; cases h
  | append_singleton l₀ a ih =>
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₀', b, rfl⟩
      · rw [spine_concat, spine_nil] at h; cases h
      · rw [List.concat_eq_append, spine_concat, spine_concat] at h
        injection h with h₁ h₂
        obtain ⟨hxy, rfl⟩ := ih h₁
        subst h₂
        exact ⟨hxy, by simp⟩

/-! ## β-reduction out of a spine -/

/-- A β-step out of a spine `x N₁ … Nₖ` takes place inside one of the
arguments. -/
theorem spine_fullBeta_inv {x : Var} {l : List (Term Var)} {N : Term Var}
    (h : FullBeta (spine x l) N) :
    ∃ l', N = spine x l' ∧ List.Forall₂ (Relation.ReflTransGen FullBeta) l l' := by
  induction l using List.reverseRecOn generalizing N with
  | nil =>
      rw [spine_nil] at h
      cases h with
      | base hb => cases hb
  | append_singleton l₀ b ih =>
      rw [spine_concat] at h
      rcases fullBeta_app_inv h with ⟨C, hC, _⟩ | ⟨b', rfl, hb⟩ | ⟨A', rfl, hA⟩
      · exact absurd hC spine_ne_abs
      · exact ⟨l₀ ++ [b'], by rw [spine_concat],
          forall₂_betaStar_concat (forall₂_betaStar_refl l₀)
            (Relation.ReflTransGen.single hb)⟩
      · obtain ⟨l₁, rfl, hl₁⟩ := ih hA
        exact ⟨l₁ ++ [b], by rw [spine_concat],
          forall₂_betaStar_concat hl₁ Relation.ReflTransGen.refl⟩

/-- Any number of β-steps out of a spine `x N₁ … Nₖ` only reduce the arguments:
the reduct is a spine with the same head and componentwise β-reducts as
arguments. -/
theorem spine_fullBetaStar_inv {x : Var} {l : List (Term Var)} {N : Term Var}
    (h : (Relation.ReflTransGen FullBeta) (spine x l) N) :
    ∃ l', N = spine x l' ∧ List.Forall₂ (Relation.ReflTransGen FullBeta) l l' := by
  induction h with
  | refl => exact ⟨l, rfl, forall₂_betaStar_refl l⟩
  | tail _ hstep ih =>
      obtain ⟨l₁, rfl, hl₁⟩ := ih
      obtain ⟨l₂, rfl, hl₂⟩ := spine_fullBeta_inv hstep
      exact ⟨l₂, rfl, forall₂_betaStar_trans hl₁ hl₂⟩

theorem beta_steps_preserve_fvar_apps {x : String} {M : Term String}
    {l : List (Term String)} (steps : l.foldl app (fvar x) ↠βᶠ M) :
    ∃ l' : List _, M = l'.foldl app (fvar x) ∧
      List.Forall₂ (Relation.ReflTransGen FullBeta) l l' :=
  spine_fullBetaStar_inv (x := x) (l := l) steps


/-- A head neutral term is a spine headed by a free variable. -/
theorem HeadNeutral.exists_spine {M : Term Var} (h : HeadNeutral M) :
    ∃ (x : Var) (l : List (Term Var)), M = spine x l := by
  induction h with
  | fvar x => exact ⟨x, [], rfl⟩
  | @app A B _ _ ih =>
      obtain ⟨x, l, rfl⟩ := ih
      exact ⟨x, l ++ [B], by rw [spine_concat]⟩

/-! ## The main theorem -/

/-- **A head normal form that β-reduces to a variable-headed spine is already
such a spine.**  If `M` is a head normal form and `M ↠β x N₁ … Nₖ`, then
`M = x N'₁ … N'ₖ` for arguments `N'ᵢ` with `N'ᵢ ↠β Nᵢ`. -/
theorem steps_headnf_preserve_multiapp {x : Var} {M : Term Var} {l : List (Term Var)}
    (h_normal : HeadNF M) (steps : M ↠βᶠ l.foldl app (fvar x)) :
    ∃ l' : List (Term Var), M = l'.foldl app (fvar x) ∧
      List.Forall₂ (Relation.ReflTransGen FullBeta) l' l := by
  have steps' : (Relation.ReflTransGen FullBeta) M (spine x l) := steps
  have hnotabs : ¬ M.IsAbs := by
    intro hab
    cases hab
    obtain ⟨T', hT⟩ := fullBetaStar_abs_inv steps
    exact spine_ne_abs hT
  obtain ⟨y, l₀, rfl⟩ := (h_normal.of_not_isAbs hnotabs).exists_spine
  obtain ⟨l', hN, hF⟩ := spine_fullBetaStar_inv steps'
  obtain ⟨rfl, rfl⟩ := spine_inj hN.symm
  exact ⟨l₀, rfl, hF⟩
