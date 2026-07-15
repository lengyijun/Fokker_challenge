import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LeftmostReduction
-- import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.MultiApp
import Cslib.Foundations.Data.HasFresh
import FokkerChallenge.Basic
import FokkerChallenge.EnhancedCslib.LeftMost
import FokkerChallenge.EnhancedCslib.BetaNormalForm
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

/-
theorem genFinset_list (fs : Finset (Term String))
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough) {t} (ht: GenFinset fs t) :
  ∃ (l : List (Term String)) (f : Term String),
    t = l.foldl Term.app (f.abs.abs) /\
    f.abs.abs ∈ fs /\
    ∀ x ∈ l, GenFinset fs x := by
  induction ht with
  | base atom h =>  exists []
                    specialize h2 _ h
                    unfold abs_two_vars_are_enough at h2
                    split at h2 <;> grind
  | @app M N _ _ ihm ihn =>
    obtain ⟨l, f, _⟩ := ihm
    refine ⟨l ++ [N], f, ?_⟩
    grind
-/

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


/-
@[scoped grind]
inductive leftSpine (fs : Finset (Term String)) : Term String → Prop where
  | singleton : ∀ t ∈ fs, leftSpine fs t
  | leftApp   : ∀ t1 ∈ fs, ∀ t2, GenFinset fs t2 → leftSpine fs (t1.app t2)

theorem genFinset_of_reduces {fs : Finset (Term String)} {a b f t' t'': Term String} {l}
  (h : GenFinset fs ((a :: b :: l).foldl Term.app f.abs.abs)):
  ((a :: b :: l).foldl Term.app f.abs.abs) ⭢ℓ t'  ->
  t' ⭢ℓ t'' ->
  GenFinset fs t''
  := by
  sorry
-/



axiom BetaAt.unique {M N Q: Term String} {i} : BetaAt i M N -> BetaAt i M Q -> N = Q

axiom BetaAt.step_fv {M N: Term String} {i} : BetaAt i M N -> N.fv ⊆ M.fv

@[reduction_sys "ℓℓ"]
inductive Leftmost2 : Term String → Term String → Prop
  | base {M1 M2 M3 N Q} : Leftmost (Term.app (Term.app M1 M2) M3) N ->
                          Leftmost N Q ->
                          Leftmost2 (Term.app (Term.app M1 M2) M3) Q

@[scoped grind]
axiom Leftmost2.steps_fv {M N: Term String} : Relation.ReflTransGen Leftmost2 M N -> N.fv ⊆ M.fv

lemma step_lc_r {M M' : Term String} (redex : M ⭢ℓℓ M') : LC M -> LC M' := by
  cases redex
  grind [BetaAt.lc_r]

@[scoped grind]
lemma steps_lc_r {M M' : Term String} (redex : M ↠ℓℓ  M') : LC M -> LC M' := by
  induction redex with grind [step_lc_r]

@[scoped grind]
theorem leftmostMulti_to_multi {M N} (h : M ↠ℓℓ N) : M ↠ℓ N := by
  induction h with
  | refl => grind
  | tail h1 h2 h3 =>  cases h2 with | base h4 h5 =>
                      refine .trans h3 (.trans (.single h4) (.single h5))


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


/-
theorem no_P_reduct {fs : Finset (Term String)}
  (h2 :  ∀ t ∈ fs, t.abs_two_vars_are_enough)
  (hfv : ∀ t ∈ fs, t.fv = ∅) {t}
  (ht: GenFinset fs t)
  (hnormal : Relation.Normalizable FullBeta ((t.app (fvar "x")).app (fvar "y")))
  (hp : ∀ t', t ↠ℓ t' -> P fs t') : False := by
  obtain ⟨N, h1, h3⟩ := hnormal
  rw [<- foo] at h3
  have h4 := Leftmost.normalization (by grind) h1 h3
  have h: ∀ (t' : Term String), t ↠ℓ t' → (t.app (fvar "x")).app (fvar "y") ↠ℓ (t'.app (fvar "x")).app (fvar "y") := by
    intros t' _
    apply Leftmost.steps_app_l_cong
    apply Leftmost.steps_app_l_cong
    · grind
    · specialize hp t' (by assumption)
      obtain ⟨l, _, _, _, _, _, _⟩ := hp
      induction l using List.reverseRecOn with grind [IsAbs]
    · grind [IsAbs]
  induction h4 with
  | refl => obtain ⟨_, h3, _⟩ := BetaNormal.app_inv h3
            obtain ⟨_, h3, _⟩ := BetaNormal.app_inv h3
            sorry
  | tail _ _ _ => sorry
-/

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
              obtain ⟨_, _, _⟩ := hnormal
              sorry
  rw [<- genfinset_P]
  apply gen_abs_2_vars_are_enough ht
  grind
  apply subterms_two_vars_are_enough (abs_two_vars_are_enough_weak h2)



end LambdaCalculus.LocallyNameless.Untyped.Term

end Cslib
