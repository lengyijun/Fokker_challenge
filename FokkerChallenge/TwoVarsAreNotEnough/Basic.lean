import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.ListFullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.FamousCombinator
import FokkerChallenge.EnhancedCslib.Basic
import FokkerChallenge.EnhancedCslib.LeftMost
import FokkerChallenge.EnhancedCslib.BetaNormalForm
import FokkerChallenge.EnhancedCslib.Closedunderapp
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind =]
def two_vars_are_enough: Term String → Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => false
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | Term.app t1 t2 => two_vars_are_enough t1 && two_vars_are_enough t2
  | _ => false

@[scoped grind]
theorem two_vars_are_enough_lc {t} (g : two_vars_are_enough t) : t.abs.abs.LC := by
  rw [<- lcAt_iff_LC]
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n ih => cases t with
  | fvar => grind
  | bvar => grind
  | app => grind
  | abs t => cases t with
    | bvar => grind
    | fvar => grind
    | app => grind
    | abs t =>  specialize @ih _ ?_ t ?_ rfl
                grind
                grind
                unfold LcAt
                unfold LcAt
                refine lcAt_le _ _ _ (by omega) ih


/-
theorem two_vars_are_enough_openRec {i x t} (g : two_vars_are_enough t) :
  two_vars_are_enough (t⟦i ↝ fvar x⟧) := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind
-/

@[scoped grind =]
def subterms : Term String -> Finset (Term String)
  | Term.bvar _ => ∅
  | Term.fvar _ => ∅
  | Term.abs (Term.abs t) => insert t.abs.abs (subterms t)
  | Term.abs _ => ∅
  | Term.app t1 t2 => subterms t1 ∪ subterms t2

theorem subterms_subset {t : Term String} :
    ∀ s ∈ t.subterms, s.subterms ⊆ t.subterms := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind

@[scoped grind]
theorem subterms_size {t} :
    ∀ s ∈ subterms t, s.fokker_size <= t.fokker_size := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind

theorem subterms_gen {t M} (h : Gen t M) : t.subterms = M.subterms := by
  induction h with grind

theorem subterms_fv {t} (h : t.fv = ∅) :
    ∀ s ∈ subterms t, s.fv = ∅ := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
      | bvar _ => grind
      | fvar _ => grind
      | app _ _ => grind
      | abs t => cases t with grind

theorem subterms_preserved_under_openRec {x i t} (h : two_vars_are_enough t) :
    t.subterms = t⟦i ↝ fvar x⟧.subterms := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ => grind
    | abs t => cases t with grind

@[scoped grind =]
def abs_two_vars_are_enough: Term String → Bool
  | Term.abs (Term.abs t) => two_vars_are_enough t
  | _ => false

theorem abs_two_vars_are_enough_weak {t} (h: abs_two_vars_are_enough t) : t.two_vars_are_enough := by
  unfold abs_two_vars_are_enough at h
  grind

@[scoped grind]
theorem abs_two_vars_are_enough_lc {t} (h: abs_two_vars_are_enough t) : t.LC := by
  unfold abs_two_vars_are_enough at h
  split at h <;> grind

@[scoped grind]
theorem subterms_two_vars_are_enough {t} (h : two_vars_are_enough t) :
    ∀ s ∈ subterms t, abs_two_vars_are_enough s := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
      | bvar _ => grind
      | fvar _ => grind
      | app _ _ => grind
      | abs t => cases t with grind

theorem two_vars_are_enough_subterms_lc {t} (h : two_vars_are_enough t) :
    ∀ s ∈ subterms t, s.LC := by grind


@[scoped grind =]
def idempotent (terms : Finset (Term String)) : Prop :=
  terms.biUnion subterms = terms

theorem subterms_idempotent {t : Term String} : idempotent t.subterms := by
    induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
    | h n _ => cases t with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ => grind
    | abs t => cases t with grind

@[scoped grind]
inductive GenFinset (atoms: Finset (Term String)) : Term String → Prop where
  | base : ∀ atom ∈ atoms, GenFinset atoms atom
  | app {M N}  : GenFinset atoms M → GenFinset atoms N → GenFinset atoms (app M N)

@[scoped grind]
theorem genFinset_lc (fs : Finset (Term String))
  (h2 :  ∀ t ∈ fs, t.LC) {t} (ht: GenFinset fs t) : t.LC := by
  induction ht with grind

@[scoped grind]
theorem genFinset_fv (fs : Finset (Term String))
  (hfv : ∀ t ∈ fs, t.fv = ∅)
   {t} (ht: GenFinset fs t) : t.fv = ∅ := by
  induction ht with grind

theorem gen_abs_2_vars_are_enough {atom M : Term String} (h : Gen atom M) (g : atom.abs_two_vars_are_enough):
  GenFinset atom.subterms M := by
  induction h with
  | base => apply GenFinset.base
            unfold abs_two_vars_are_enough at g
            grind
  | app _ _ _ _ => grind


theorem genFinset_open2 (fs : Finset (Term String))
  (h2 :  ∀ t ∈ fs, t.LC)
  {x : Term String}
  (hx : x.two_vars_are_enough)
  (hsubset : x.subterms ⊆ fs)
  (hfv : x.fv = ∅) :
  ∀ y z, GenFinset fs y -> GenFinset fs z -> GenFinset fs (x⟦1 ↝ y⟧⟦0 ↝ z⟧) := by
  induction h : x.fokker_size using Nat.strong_induction_on generalizing x with
  | h n ih => cases x with intros y z hy hz
  | bvar n => clear ih
              rw [openRec_bvar]
              split
              . rw [open_lc] <;> grind
              . grind
  | fvar _ => simp at hfv
  | app _ _ =>  rw [openRec_app]
                apply GenFinset.app <;> apply ih
                any_goals rfl
                all_goals grind
  | abs t => cases t with
    | bvar _ => clear ih; grind
    | fvar _ => clear ih; grind
    | app _ _ => clear ih; grind
    | abs t =>  rw [open_lc, open_lc]
                · apply GenFinset.base
                  grind
                · grind
                · rw [open_lc] <;> grind

theorem genFinset_list (fs : Finset (Term String))
  {f} {l : List (Term String)}
  (ht: GenFinset fs f)
  (hl : ∀ x ∈ l, GenFinset fs x) : GenFinset fs (l.foldl Term.app f) := by
  induction l generalizing f with grind

@[scoped grind]
def spine : Term String → Term String × List (Term String)
  | Term.app f a => let (h, args) := spine f; (h, args ++ [a])
  | t            => (t, [])

theorem spine_def {t l f} : spine t = (f, l) -> l.foldl Term.app f = t := by
  induction t generalizing l f with grind

theorem spine_def_2 (t : Term String) : t.spine.2.foldl Term.app t.spine.1 = t := by
  induction t with grind

@[scoped grind]
def P (fs : Finset (Term String)) (t : Term String) : Prop :=
  let (h, args) := spine t
  h ∈ fs /\ ∀ x ∈ args, GenFinset fs x


@[scoped grind]
theorem genfinset_P {fs : Finset (Term String)}
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  {t: Term String} :
  GenFinset fs t <-> P fs t := by
  constructor
  . intros h
    induction h with
    | base atom _ =>  unfold P
                      split
                      rename_i h _ _ _ heq
                      unfold spine at heq
                      split at heq <;> grind
    | app _ _ _ _ => grind
  . intros h
    unfold P at h
    split at h
    rename_i l _
    induction t generalizing l with grind


@[scoped grind]
theorem P_fv(fs : Finset (Term String))
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
   {t} (ht: P fs t) : t.fv = ∅ := by
  apply genFinset_fv _ hfv
  rw [genfinset_P]
  grind
  grind



axiom BetaAt.unique {M N Q: Term String} {i} : BetaAt i M N -> BetaAt i M Q -> N = Q

axiom BetaAt.step_fv {M N: Term String} {i} : BetaAt i M N -> N.fv ⊆ M.fv

@[reduction_sys "𝒽"]
inductive HeadReduction : Term String → Term String → Prop
  | base {M N1 N2: Term String} : HeadReduction ((M.abs.abs.app N1).app N2) (M⟦1 ↝ N1⟧⟦0 ↝ N2⟧)
  | appL {N M1 M2: Term String} : HeadReduction M1 M2 -> HeadReduction (M1.app N) (M2.app N)

theorem HeadReduction.step_2_beta {M N : Term String} (h : HeadReduction M N) (m_lc : M.LC) : M ↠βᶠ N := by
  induction h with
  | base => apply Relation.ReflTransGen.head
            apply Xi.appR
            grind [cases LC]
            apply Xi.base
            constructor
            grind [cases LC]
            grind [cases LC]
            apply Relation.ReflTransGen.single
            apply Xi.base
            constructor
            . cases m_lc with | app m_lc _ => cases m_lc with | app _ n_lc =>
              rw [<- lcAt_iff_LC] at *
              unfold LcAt
              rw [lcAt_openRec_iff_lcAt]
              grind
              apply lcAt_le _ _ _ (by omega) n_lc
            . grind [cases LC]
  | appL _ _ => apply FullBeta.redex_app_l_cong <;> grind [cases LC]

theorem HeadReduction.steps_2_beta {M N : Term String} (h : Relation.ReflTransGen HeadReduction M N) (m_lc : M.LC) : M ↠βᶠ N := by
  induction h with
  | refl => grind
  | tail _ h ih =>
      apply HeadReduction.step_2_beta at h
      cases FullBeta.steps_lc_or_rfl ih with
      | inl h =>  refine .trans (by assumption) ?_
                  grind
      | inr h => grind

theorem HeadReduction.step_lc_r {M N : Term String}
  (h : Relation.ReflTransGen HeadReduction M N)
  (m_lc : M.LC) : N.LC := by
  grind [HeadReduction.steps_2_beta, FullBeta.steps_lc_or_rfl]

theorem head_multiapp (f a b: Term String) (l) :
  (a :: b :: l).foldl Term.app f.abs.abs ⭢𝒽 l.foldl Term.app (f⟦1 ↝ a⟧⟦0 ↝ b⟧) := by
  induction l using List.reverseRecOn generalizing f a with simp
  | nil => refine .base
  | append_singleton l a _ => refine .appL (by grind)

theorem head_fvar {l : List (Term String)} {M : Term String} {x : String} :
  l.foldl Term.app (fvar x) ⭢𝒽 M -> False := by
  induction h : l.length using Nat.strong_induction_on generalizing M l with | h n ih =>
  intros g
  cases (List.eq_nil_or_concat' l) with
  | inl h =>  subst_vars
              cases g
  | inr h =>  obtain ⟨l, b, h⟩ := h
              subst_vars
              rw [List.foldl_concat] at g
              cases (List.eq_nil_or_concat' l) with
              | inl h =>  subst_vars
                          simp at g
                          cases g
                          rename_i g
                          cases g
              | inr h =>  obtain ⟨l, a, h⟩ := h
                          subst_vars
                          rw [List.foldl_concat] at g
                          generalize heq : l.foldl Term.app (fvar x) = Y
                          rw [heq] at g
                          cases g with
                          | base => cases (List.eq_nil_or_concat' l) with subst_vars
                            | inl h =>  simp at heq
                            | inr h =>  obtain ⟨l, b, h⟩ := h
                                        subst_vars
                                        rw [List.foldl_concat] at heq
                                        cases heq
                          | appL g => cases g with
                            | base => cases (List.eq_nil_or_concat' l) with subst_vars
                              | inl h =>  simp at heq
                              | inr h =>  obtain ⟨l, b, h⟩ := h
                                          subst_vars
                                          rw [List.foldl_concat] at heq
                                          generalize heq2 : l.foldl Term.app (fvar x) = Z
                                          rw [heq2] at heq
                                          cases heq
                                          cases (List.eq_nil_or_concat' l) with subst_vars
                                          | inl h =>  simp at heq2
                                          | inr h =>  obtain ⟨l, b, h⟩ := h
                                                      subst_vars
                                                      rw [List.foldl_concat] at heq2
                                                      cases heq2
                            | appL g => rw [<- heq] at g
                                        apply ih _ _ rfl g
                                        simp

theorem foldl_multiapp_cases {f M : Term String} {l : List (Term String)}
  (g : HeadReduction (l.foldl app f) M):
  (∃ f', HeadReduction f f' /\ M = l.foldl app f') \/
  (∃ a b l' f', l = b :: l'      /\ f = f'.abs.abs.app a /\ M = l'.foldl app (f'⟦1 ↝ a⟧⟦0 ↝ b⟧)) \/
  (∃ a b l' f', l = a :: b :: l' /\ f = f'.abs.abs       /\ M = l'.foldl app (f'⟦1 ↝ a⟧⟦0 ↝ b⟧))
  := by
  induction h : l.length using Nat.strong_induction_on generalizing M l f with | h n ih =>
  cases l with
  | nil => grind
  | cons head l =>
      simp at g
      cases l with simp at g
      | nil => cases g <;> grind
      | cons head tail =>
        specialize ih _ ?_ g rfl
        . simp at h
          omega
        . rcases ih with ⟨f, ih, _⟩|ih|ih
          . cases ih with
          | base => grind
          | appL ih => cases ih <;> grind
          . grind
          . grind


@[scoped grind]
inductive unroll_inner : Term String → Term String → Prop
  | reflTrans {M N: Term String} : Relation.ReflTransGen HeadReduction M N -> unroll_inner M N
  | throughAbsApp {M N1 N2: Term String} : Relation.ReflTransGen HeadReduction M (N1.abs.app N2) -> unroll_inner M N2

@[scoped grind]
def unroll : Term String → Term String → Prop := Relation.ReflTransGen unroll_inner

@[scoped grind]
theorem unroll_lc {M N : Term String}
  (m_lc: M.LC) (hmn : unroll M N): N.LC := by
  induction hmn with
  | refl => grind
  | tail _ h ih => cases h with
  | reflTrans h => apply HeadReduction.step_lc_r h ih
  | throughAbsApp h => cases HeadReduction.step_lc_r h ih with | app _ _ => grind

@[scoped grind]
def fvar_or_combinator (a: Term String) : Prop :=  a.IsFvar \/ a.abs_two_vars_are_enough

theorem unroll_2_vars_are_enough {M N : Term String}
  (hm : ClosedUnderApp fvar_or_combinator M)
  (hmn : unroll M N):
  ∃ l: List (Term String), M ↠βᶠ l.foldl app N /\ ∀ x ∈ l, x.abs_two_vars_are_enough := by
  induction hmn with
  | refl => exists []
  | tail g h ih => cases h with
    | reflTrans h =>
    apply HeadReduction.steps_2_beta at h
    specialize h (unroll_lc (closedunderapp_lc (by grind) hm) g)
    obtain ⟨l, ih, g⟩ := ih
    exact ⟨l, .trans ih (steps_multiApp_l h (by grind)), g⟩
    | throughAbsApp _ => sorry

/-
theorem unroll_def {M N : Term String} : unroll M N ->
  ∃ (l : List (Term String)), M = l.foldl Term.app N /\ ∀ x ∈ l, x.depth <= M.depth := by
  sorry
-/

@[scoped grind]
def head_secure (M : Term String) := ∃ Y, ((M.app (fvar "x")).app (fvar "y")) ↠ℓ ((fvar "x").app Y)


@[scoped grind]
def Q (mx a: Term String) : Prop := a = (fvar "y") \/
                                    unroll mx a \/
                                    (a.abs_two_vars_are_enough /\ a.depth < mx.depth)

@[scoped grind]
def T (a: Term String) : Prop :=  a = (fvar "y") \/
                                  a = (fvar "x") \/
                                  a.abs_two_vars_are_enough

theorem closedUnderApp_unroll {M N}
  (h_secure: head_secure M):
  ClosedUnderApp T M ->
  (M.app (fvar "x")).app (fvar "y") ↠𝒽 N ->
  ClosedUnderApp (Q (M.app (fvar "x"))) N := by
  intro _ g
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
        refine .trans h4 (.single (.reflTrans ?_))
        grind
      . subst_vars
        apply closedunderapp_multiapp_cons (by grind)
        sorry -- depth
      . exfalso
        subst_vars
        obtain ⟨Y, h_secure⟩ := h_secure
        sorry -- fvar
    . unfold abs_two_vars_are_enough at h4
      split at h4 <;> try grind
      subst_vars
      rcases foldl_multiapp_cases h2 with ⟨f', h2, _⟩|⟨a, b, l', f', _, h2, _⟩|⟨a, b, l', f', _, h3, h2⟩
      . cases h2
      . cases h2
      . cases h3
        subst_vars
        sorry -- depth

/-
@[scoped grind]
axiom Leftmost2.steps_fv {M N: Term String} : Relation.ReflTransGen Leftmost2 M N -> N.fv ⊆ M.fv

theorem size_dichotomy (t : Term String) :
    (∀ t', t ↠ℓℓ t' → t'.spine.2.length ≥ 2) ∨
    (∃ t', t ↠ℓℓ t' ∧ (t'.spine.2.length = 0 ∨ t'.spine.2.length = 1)) := by
  by_cases h : ∃ t', t ↠ℓℓ t' ∧ t'.spine.2.length ≤ 1
  · right
    obtain ⟨t', hstep, hsize⟩ := h
    exact ⟨t', hstep, by omega⟩
  · left
    intro t' hstep
    by_contra hcon
    exact h ⟨t', hstep, by omega⟩

lemma step_lc_r {M M' : Term String} (redex : M ⭢ℓℓ M') : LC M -> LC M' := by
  cases redex
  grind

@[scoped grind]
lemma steps_lc_r {M M' : Term String} (redex : M ↠ℓℓ  M') : LC M -> LC M' := by
  induction redex with grind

@[scoped grind]
theorem leftmostMulti_to_multi {M N} (h : M ↠ℓℓ N) : M ↠βᶠ N := by
  induction h with
  | refl => grind
  | tail h1 h2 h3 =>  cases h2 with


theorem leftmost2_preserves_P_l {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t': Term String}
  (step : t ⭢ℓℓ t')
  (h5 : P fs t) :
  P fs t' := by
  cases step with | base h4 h7 =>
  rename_i M1 M2 M3 N
  have h6 := spine_def_2 ((M1.app M2).app M3)
  generalize hl: ((M1.app M2).app M3).spine.2 = l
  rw [hl] at h6
  rw [<- h6] at h4
  cases l <;> try grind
  rename_i a l
  cases l <;> try grind
  rename_i b l
  have h7 := h2 ((M1.app M2).app M3).spine.1 (by grind)
  unfold abs_two_vars_are_enough at h7
  split at h7 <;> try grind
  rename_i f heq
  rw [heq] at h4
  have : GenFinset fs a := by grind
  have : GenFinset fs b := by grind
  have h8 := leftmost_multiapp f.abs a (b::l) (by grind) (by grind)
  have := BetaAt.unique h8 h4
  subst N
  have h8 := leftmost_multiapp (f⟦1 ↝ a⟧) b l (by grind) (by grind)
  have := BetaAt.unique h8 h7
  rw [<- genfinset_P]
  subst t'
  apply genFinset_list
  apply genFinset_open2
  all_goals grind


theorem step_leftmost2_preserves_P_r {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t': Term String}
  (step : t ⭢ℓℓ t')
  (pt: P fs t):
  P fs t' := by
  cases t with
  | bvar _ => grind
  | fvar _ => grind
  | abs _ =>  cases step
  | app M _ => cases M with
    | bvar _ => grind
    | fvar _ => grind
    | app _ _ =>  apply leftmost2_preserves_P_l
                  any_goals grind
                  · exact step
                  · grind
    | abs _ =>  cases pt with | intro left right =>
                specialize h2 _ left
                unfold abs_two_vars_are_enough at h2
                split at h2 <;> try grind
                rename_i heq
                rw [heq] at step
                cases step

theorem steps_leftmost2_preserves_P_r {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t': Term String}
  (steps : t ↠ℓℓ t')
  (pt: P fs t):
  P fs t' := by
  induction steps with grind [leftmost2_preserves_P_l]

theorem leftmost_rtc_cases {M N}
  (h : ∀ t', M ↠ℓℓ t' → t'.spine.2.length ≥ 2)
  (hmn : M ↠ℓ N) : M ↠ℓℓ N \/ ∃ Q, M ↠ℓℓ Q /\ Q ⭢ℓ N := by
  induction hmn with
  | refl => grind
  | tail _ _ ih => cases ih with
  | inl => grind
  | inr ih => left
              obtain ⟨Q, hmq, hqb⟩ := ih
              refine .trans (by assumption) (.single ?_)
              specialize h _ hmq
              have h3 := spine_def_2 Q
              generalize hq : Q.spine.2 = l
              cases (List.eq_nil_or_concat' l) <;> try grind
              rename_i heq
              obtain ⟨L, b, _⟩ := heq
              subst l
              rename_i heq
              rw [heq] at h3
              rw [List.foldl_concat] at h3
              cases (List.eq_nil_or_concat' L) <;> try grind
              rename_i heq
              obtain ⟨l, b, _⟩ := heq
              subst L
              rw [List.foldl_concat] at h3
              rw [<- h3]
              rw [<- h3] at hqb
              constructor <;> assumption

theorem leftmost2_neither_abs_nor_beta_normal {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  (t : Term String)
  (ht : P fs t)
  (h : ∀ t', t ↠ℓℓ t' → t'.spine.2.length ≥ 2) :
  ∀ t'', t ↠ℓ t'' → ¬ t''.IsAbs /\ ¬ t''.BetaNormal := by
  intros t'' g
  cases (leftmost_rtc_cases h g) with
  | inl g =>  specialize h _ g
              have h3 := spine_def_2 t''
              generalize heq: t''.spine.2 = l
              rw [heq] at h3 h
              constructor
              . grind [IsAbs, BetaNormal]
              . cases l <;> try grind
                rename_i l
                cases l <;> try grind
                have : GenFinset fs t := by grind
                have : t.LC := by grind
                apply normal_app
                · grind
                · grind
                · apply Leftmost2.steps_fv at g
                  grind
  | inr g =>  obtain ⟨t', g, g2⟩ := g
              have : t.fv = ∅ := by grind
              have : t'.fv = ∅ := by apply Leftmost2.steps_fv at g; grind
              have : t''.fv = ∅ := by apply BetaAt.step_fv at g2; grind
              specialize h _ g
              have h3 := spine_def_2 t'
              generalize heq: t'.spine.2 = l
              rw [heq] at h h3
              cases l <;> try grind
              rename_i a l
              cases l <;> try grind
              rename_i b l
              rw [<- h3] at g2
              have : GenFinset fs t := by grind
              have : P fs t := by grind
              have : t.LC := by grind
              have : t'.LC := by grind
              have : t''.LC := by grind [BetaAt.lc_r]
              have : t.spine.1 ∈ fs := by grind
              have := steps_leftmost2_preserves_P_r hidempotent h2 hfv g (by grind)
              have h3 := h2 t'.spine.1 (by grind)
              unfold abs_two_vars_are_enough at h3
              split at h3 <;> try grind
              rename_i heq
              rw [heq] at g2
              rename_i t
              have : GenFinset fs a := by grind
              have h4 := leftmost_multiapp t.abs a (b :: l) (by grind) (by grind)
              have heq := BetaAt.unique h4 g2
              constructor
              . induction l using List.reverseRecOn with grind [IsAbs, BetaNormal]
              . induction l using List.reverseRecOn with
                | nil =>  intro hnormal
                          unfold List.foldl at heq
                          unfold List.foldl at heq
                          unfold open' openRec at heq
                          subst t''
                          apply BetaNormal.app_inv at hnormal
                          grind
                | append_singleton l a _ =>
                          unfold List.foldl at heq
                          rw [List.foldl_concat] at heq
                          apply normal_app <;> grind


theorem P_progress_to_simple_spine_or_stuck_nonabs {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t} (ht: P fs t)
  : (∃ t', t ↠ℓ t' /\ P fs t' /\ (t'.spine.2.length = 0 ∨ t'.spine.2.length = 1)) \/ (∀ t', t ↠ℓ t' -> ¬ IsAbs t' /\ ¬ BetaNormal t') := by
  cases size_dichotomy t with
  | inl h => right
             apply leftmost2_neither_abs_nor_beta_normal hidempotent h2 hfv _ ht h
  | inr h =>  left
              obtain ⟨t', h, _⟩ := h
              refine ⟨t', by grind, steps_leftmost2_preserves_P_r hidempotent h2 hfv h ht, by grind⟩



theorem exists_leftSpine_reduct {atom : Term String}
  (h2: atom.abs_two_vars_are_enough)
  (hfv : atom.fv = ∅)
  {t}
  (ht : Gen atom t)
  (hnormal: Relation.Normalizable Leftmost ((t.app (fvar "x")).app (fvar "y"))) :
  ∃ t', t ↠ℓ t' /\ P atom.subterms t' /\ (t'.spine.2.length = 0 ∨ t'.spine.2.length = 1) := by
  have h := @P_progress_to_simple_spine_or_stuck_nonabs atom.subterms subterms_idempotent (subterms_two_vars_are_enough (abs_two_vars_are_enough_weak h2)) (subterms_fv hfv) t ?_
  cases h with
  | inl h => grind
  | inr h =>  exfalso
              cases normalizable_app_implies_normalizable_or_reduces_to_abs hnormal with
      | inr h3 => obtain ⟨M, _, g⟩ := h3
                  cases leftstar_cases g <;> grind
      | inl h3 => cases normalizable_app_implies_normalizable_or_reduces_to_abs h3 with
      | inr h3 => grind
      | inl h3 => obtain ⟨t'', h3, _⟩ := h3
                  obtain ⟨_, h⟩ := h t'' h3
                  apply h
                  rw [betanormal_iff]
                  sorry
  rw [<- genfinset_P]
  apply gen_abs_2_vars_are_enough ht
  grind
  apply subterms_two_vars_are_enough (abs_two_vars_are_enough_weak h2)


-- this should be trival
-- I am blocked by next theorems
theorem exists_leftSpine_reduct2 {fs : Finset (Term String)}
  (hidempotent : idempotent fs)
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t} (ht: P fs t)
  {t head : Term String}
  (hh : head ∈ fs)
  (ht : GenFinset fs t)
  (hnormal: Relation.ReflTransGen Leftmost (((head.app t).app (fvar "x")).app (fvar "y"))
                                           (((fvar "x").app (fvar "y")).app (H 100))) :
  ∃ head' t', head' ∈ fs /\ ((head.app t).app (fvar "x")) ↠ℓ head'.app t' /\ P fs t' := by
  sorry
-/

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
