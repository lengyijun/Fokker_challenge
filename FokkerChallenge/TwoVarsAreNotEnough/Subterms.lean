import FokkerChallenge.TwoVarsAreNotEnough.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

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

/-
theorem subterms_gen {t M} (h : Gen t M) : t.subterms = M.subterms := by
  induction h with grind
-/

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
