
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullEta
import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.EtaPostpone
import FokkerChallenge.EnhancedCslib.EtaToSpine

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

universe u

open Term

variable {Var : Type u} [DecidableEq Var]

theorem fv_absN (n : ℕ) (t : Term Var) : fv (abs^[n] t) = fv t := by
  induction n with
  | zero => rfl
  | succ m ih =>  rw [add_comm, Function.iterate_add]
                  simp
                  grind

theorem absn_openrec {i n} {N M : Term String} :
  (abs^[n] M)⟦i ↝ N⟧ = abs^[n] (M⟦n+i ↝ N⟧) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih => simp; grind

theorem absn_lcat {i n} {M : Term String} :
  LcAt i (abs^[n] M) = LcAt (n+i) M := by
  induction n generalizing M with
  | zero => simp
  | succ n ih => simp; grind
