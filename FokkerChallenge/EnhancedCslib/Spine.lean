import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Basic

namespace Cslib

namespace LambdaCalculus.LocallyNameless.Untyped.Term

@[scoped grind]
def spine : Term String → Term String × List (Term String)
  | Term.app f a => let (h, args) := spine f; (h, args ++ [a])
  | t            => (t, [])

theorem spine_def {t l f} : spine t = (f, l) -> l.foldl Term.app f = t := by
  induction t generalizing l f with grind

theorem spine_def_2 (t : Term String) : t.spine.2.foldl Term.app t.spine.1 = t := by
  induction t with grind
