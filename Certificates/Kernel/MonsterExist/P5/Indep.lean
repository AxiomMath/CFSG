module

public import CFSG.Monster.Existence.StdOdd.P5Inputs

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem wsT_indep : ∀ c : Fin 5 → ZMod 3, ∑ i, c i • wsT i = 0 → c = 0 := by decide +kernel

theorem ws1_indep : ∀ c : Fin 4 → ZMod 3, ∑ i, c i • ws1 i = 0 → c = 0 := by decide +kernel

theorem refl_apply :
    ∀ (i : Fin 6) (v : E5), (refl i).mulVec v = v - bil v (alpha i) • alpha i := by
  decide +kernel

end CertificateChecks.MonsterExist.P5

end
