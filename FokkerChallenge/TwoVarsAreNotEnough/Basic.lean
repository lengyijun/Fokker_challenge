import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
-- import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind =]
def two_vars_are_enough: Term String → Bool
  | Term.bvar n => n < 2
  | Term.fvar _ => true
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


theorem two_vars_are_enough_openRec {i x t} (g : two_vars_are_enough t) :
  two_vars_are_enough (t⟦i ↝ fvar x⟧) := by
  induction h : t.fokker_size using Nat.strong_induction_on generalizing t with
  | h n _ => cases t with
  | bvar _ => grind
  | fvar _ => grind
  | app _ _ => grind
  | abs t => cases t with grind

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
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough) {t} (ht: GenFinset fs t) : t.LC := by
  induction ht with grind

theorem genFinset_open2 (fs : Finset (Term String))
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  {x : Term String}
  (hx : x.two_vars_are_enough)
  (hsubset : x.subterms ⊆ fs)
  (hfv : x.fv = ∅) :
  ∀ y z, GenFinset fs y -> GenFinset fs z -> GenFinset fs (x⟦0 ↝ y⟧⟦1 ↝ z⟧) := by
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

inductive leftSpine (fs : Finset (Term String)) : Term String → Prop where
  | singleton : ∀ t ∈ fs, leftSpine fs t
  | leftApp   : ∀ t1 ∈ fs, ∀ t2, GenFinset fs t2 → leftSpine fs (t1.app t2)

theorem leftmost_multiapp {f a: Term String} {l} : f.abs.LC -> a.LC ->
  (a :: l).foldl Term.app f.abs ⭢ℓ l.foldl Term.app (f^a) := by
  induction l using List.reverseRecOn generalizing f a with
  | nil => apply BetaAt.outer
  | append_singleton l a _ => intros _ _
                              simp
                              apply BetaAt.appNoAbsL
                              grind
                              intros h
                              generalize heq : (List.foldl app (f.abs.app a) l) = Q
                              rw [heq] at h
                              cases h
                              induction l using List.reverseRecOn with grind

def P (t : Term String) : Prop :=
  ∃ (l : List (Term String)) (f a b: Term String), t = (a :: b :: l).foldl Term.app f.abs.abs

theorem genFinset_of_reduces {fs : Finset (Term String)} {a b f t' t'': Term String} {l}
  (h : GenFinset fs ((a :: b :: l).foldl Term.app f.abs.abs)):
  ((a :: b :: l).foldl Term.app f.abs.abs) ⭢ℓ t'  ->
   t' ⭢ℓ t'' ->
  GenFinset fs t''
  := by
  sorry

theorem gen_leftspine {fs : Finset (Term String)}
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅)
  {t t' t'': Term String} :
    P t ->
    t  ⭢ℓ t'  ->
    t' ⭢ℓ t'' ->
  leftSpine fs t'' \/ P t'' := by
  sorry

theorem no_P_reduct {atom : Term String} (h2: atom.two_vars_are_enough) (hfv : atom.fv = ∅) {t}:
  Gen atom t ->
  Relation.Normalizable FullBeta ((t.app (fvar "x")).app (fvar "y")) ->
  ∀ t', t ↠ℓ t' -> P t' -> False := by
  sorry

theorem exists_leftSpine_reduct {atom : Term String} (h2: atom.two_vars_are_enough) (hfv : atom.fv = ∅) {t}:
  Gen atom t ->
  Relation.Normalizable FullBeta ((t.app (fvar "x")).app (fvar "y")) ->
  ∃ t', t ↠ℓ t' /\ leftSpine atom.subterms t' := by
  -- grind [no_P_reduct, gen_leftspine]
  sorry

end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
