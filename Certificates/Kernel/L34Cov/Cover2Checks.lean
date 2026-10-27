module

public import Certificates.Kernel.L34Cov.Checks
public import Certificates.Kernel.L34W.Gens
public import Certificates.Data.Kernel.L34Cov.Trans

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.GrSLit.L34Facts CertificateChecks.KernelL34W

@[expose] noncomputable def commK22206 (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Bool :=
  L.all fun d => cvId (commWord (tw d.1) (tw d.2.1)) d.2.2.1 d.2.2.2.1 d.2.2.2.2

theorem ch22206w_a : commK22206 (commData2.take 265) = true := by decide +kernel

theorem ch22206w_b : commK22206 (commData2.drop 265) = true := by decide +kernel

theorem ch22206w_f :
    fourthData2.all (fun d => cvId (wpow (tw d.1) 4) d.2.1 d.2.2.1 d.2.2.2) = true := by
  decide +kernel

theorem ch22206c_1 : cOK1 (cTab commData2) = true := by decide +kernel

theorem ch22206c_2 : cOK2 (cTab commData2) = true := by decide +kernel

theorem ch22206c_t : transK (cTab commData2) = true := by decide +kernel

theorem ch22206c_c : cceK (cTab commData2) GT = true := by decide +kernel

end CertificateChecks.KernelL34Cov

end
