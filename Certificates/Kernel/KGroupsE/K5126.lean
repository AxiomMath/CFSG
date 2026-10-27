module

public import CFSG.GH74.KGroups.M11TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 CFSG.Certificates.Kernel.PkEnum

theorem qs_5126K : schP QS = true ∧ orderV QS = 16 := by
  constructor <;> decide +kernel

theorem inv_5126K : invConjCheck (elemsV Q) t0 = true := by
  decide +kernel

theorem small_5126K : smallCheck (elemsV QS) s0 = true := by
  decide +kernel

theorem rel_5126K : sR ^ 8 = 1 ∧ sT ^ 2 = 1 ∧ sT * sR * sT⁻¹ = sR ^ 3 ∧
    (∀ i : Fin 8, ∀ e : Fin 2, sR ^ (i : ℕ) * sT ^ (e : ℕ) = 1 → i = 0 ∧ e = 0) := by
  decide +kernel

theorem le_5126K : (QS.original.toList.all fun g => siftP Q g 0) = true := by
  decide +kernel

theorem neg5126K : invConjCheck (elemsV Q) 1 = false := by
  decide +kernel

theorem neg5126K' : smallCheck (elemsV QS) 1 = false := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
