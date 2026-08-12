import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBetaEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.LcAt
import FokkerChallenge.EnhancedCslib.Closedunderapp
import FokkerChallenge.EnhancedCslib.List
import Mathlib.Data.Finset.Lattice.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

def GenFinset (atoms: List (Term String)) := ClosedUnderApp (fun t => t ∈ atoms)

def Gen (atom : Term String) := GenFinset [atom]

def not_basises (atoms : List (Term String)) : Prop :=
  ∃ y, y.LC ∧ y.fv = ∅ ∧ ∀ t, GenFinset atoms t → Relation.ReflTransGen FullBetaEta t y → False

def not_basis (atom : Term String) : Prop := not_basises [atom]

theorem genfinset_depth {fs M} (h : GenFinset fs M) :
   M.depth <= ((fs.map depth).max?).getD 0 := by
  induction h with
  | base ht =>  rename_i t
                have hle : t.depth ≤ (List.map depth fs).max?.getD 0 :=
                  List.mem_le_max?_getD (List.mem_map_of_mem ht)
                omega
  | app _ _ _ _ => unfold depth; omega
