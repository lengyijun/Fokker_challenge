import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[simp, scoped grind unfold]
def GenFinset (atoms: List (Term String)) := ClosedUnderApp (fun t => t ∈ atoms)

@[simp, scoped grind unfold]
def Gen (atom : Term String) := GenFinset [atom]

@[simp, scoped grind unfold]
def not_basises (atoms : List (Term String)) : Prop :=
  ∃ y, y.LC ∧ y.fv = ∅ ∧ ∀ t, GenFinset atoms t → t ↠βηᶠ y → False

@[simp, scoped grind unfold]
def not_basis (atom : Term String) : Prop := not_basises [atom]

theorem genfinset_depth {fs M} (h : GenFinset fs M) :
   M.depth <= ((fs.map depth).max?).getD 0 := by
  induction h with
  | base ht =>  rename_i t
                have hle : t.depth ≤ (List.map depth fs).max?.getD 0 :=
                  List.mem_le_max?_getD (List.mem_map_of_mem ht)
                omega
  | app _ _ _ _ => unfold depth; omega

theorem genfinset_subset {l1 l2 M} (hsubset : l1 ⊆ l2) (h : GenFinset l1 M) :
  GenFinset l2 M := by
  induction h <;> grind
