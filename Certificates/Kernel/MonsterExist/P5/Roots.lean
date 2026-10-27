module

public import CFSG.Monster.Existence.StdOdd.P5Inputs

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem card_rootVecs : rootVecs.card = 72 := by decide +kernel

theorem rkFibre_30_eq : rkFibre 30 = rootVecs := by decide +kernel

theorem card_rkFibre_30 : (rkFibre 30).card = 72 := by rw [rkFibre_30_eq, card_rootVecs]

theorem card_rkFibre_18 : (rkFibre 18).card = 80 := by decide +kernel

theorem card_rkFibre_24 : (rkFibre 24).card = 90 := by decide +kernel

theorem rk_cases : ∀ x : E5, x ≠ 0 → rk x = 30 ∨ rk x = 18 ∨ rk x = 24 := by decide +kernel

theorem rk_vRoot : rk vRoot = 30 := by decide +kernel

theorem rk_vSing : rk vSing = 18 := by decide +kernel

theorem rk_vNorm : rk vNorm = 24 := by decide +kernel

end CertificateChecks.MonsterExist.P5

end
