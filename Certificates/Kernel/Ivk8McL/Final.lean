module

public import Certificates.Kernel.Ivk8McL.Checks
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.Ivk8TwoNSound

public section

namespace CertificateChecks.KernelIvk8McL

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.Ivk8N Certificates.Ivk8Two.McL CertificateChecks.KernelCensus
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

theorem dims : Dims 275 9 := ⟨by decide, by decide, by decide, by decide⟩

theorem arrTable_unpack {n w : Nat} (hw : w ≤ 32) (X : Nat) :
    arrTable n (CFSG.KS.Raw.unpack n w X) = tabN n w X := by
  apply Array.ext (by simp [arrTable, tabN])
  intro i h1 _
  have hi : i < n := by simpa [arrTable] using h1
  simp only [arrTable, tabN, Array.getElem_ofFn]
  rw [getElem!_pos _ i (by simpa [CFSG.KS.Raw.unpack] using hi)]
  simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
  rw [pg_mod hi]

theorem gensT_eq : gensT = [McLS.F 0, McLS.F 1].map (tabN 275 9) := by
  unfold gensT
  rw [McLK.mclStrongArrs_get 0 (by norm_num), McLK.mclStrongArrs_get 1 (by norm_num),
    arrTable_unpack (by norm_num), arrTable_unpack (by norm_num)]
  rfl

theorem mclTwoOK_true : mclTwoOK = true := by
  unfold mclTwoOK
  rw [gensT_eq, twoOKT_tabN dims]
  exact mclTwoN_ok

end CertificateChecks.KernelIvk8McL

end
