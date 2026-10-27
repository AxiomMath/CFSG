module

public import CFSG.GH74.KGroups.L33TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Certificates.Kernel.PkEnum

theorem qs_5121K : schP QS = true ∧ orderV QS = 16 := by
  constructor <;> decide +kernel

theorem inv_5121K : invConjCheck (elemsV QP) t0 = true := by
  decide +kernel

theorem small_5121K : smallCheck (elemsV QS) s0 = true := by
  decide +kernel

theorem rel_5121K : sR ^ 8 = 1 ∧ sT ^ 2 = 1 ∧ sT * sR * sT⁻¹ = sR ^ 3 ∧
    (∀ i : Fin 8, ∀ e : Fin 2, sR ^ (i : ℕ) * sT ^ (e : ℕ) = 1 → i = 0 ∧ e = 0) := by
  decide +kernel

theorem le_5121K : (QS.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

theorem neg5121K : smallCheck (elemsV QS) t0 = false := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
