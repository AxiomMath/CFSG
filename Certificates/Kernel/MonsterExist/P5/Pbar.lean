module

public import Certificates.Kernel.MonsterExist.P5.Table

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem pmat_ra : ∀ i : Fin 81, pmat (ra i) = pmat i * aMat := by decide +kernel

theorem pmat_rb : ∀ i : Fin 81, pmat (rb i) = pmat i * bMat := by decide +kernel

theorem pmat_zero : pmat 0 = 1 := by decide +kernel

theorem walk_pw : ∀ j : Fin 81, walk (pw j) 0 = j := by decide +kernel

theorem tb_eq : ∀ i j : Fin 81, tb i j = walk (pw j) i := tb_walk

theorem tb_inv : ∀ i : Fin 81, ∃ j : Fin 81, tb i j = 0 := by
  rw [tb_eq_tbF]
  decide +kernel

end CertificateChecks.MonsterExist.P5

end
