module

public import Certificates.Kernel.HSPinned6101.Data
public import Certificates.Kernel.VecCert.HS

public section

namespace CertificateChecks.KernelHSPinned6101

open Certificates.Kernel.HSPinned6101 CertificateChecks.KernelVec.HS CFSG.KC.VecK

set_option maxRecDepth 100000

theorem lm_ok : allR 0 100 (lmAt LM) = true := by decide +kernel

theorem inj_ok : allR 0 100 (fun i => allR 0 100 (injAt LM i)) = true := by decide +kernel

theorem wit_ok : allR 0 20 (witAt LM) = true := by decide +kernel

theorem stars_ok : allR 0 100 (starAt (lk AT 32) (lk BT 32) VAB) = true := by decide +kernel

theorem adj_zero_four : adjK LM 0 4 = true := by decide +kernel

theorem not_adj_zero_one : adjK LM 0 1 = false := by decide +kernel

open CFSG.Sporadic.Recognition.HSPinned.Native in
theorem vtx_lt : ∀ i < 100, vtxA[i]! < 100 ∧ vtxB[i]! < 100 := by decide +kernel

open CFSG.Sporadic.Recognition.HSPinned.Native in
theorem tree_ok : ∀ i < 100, 0 < i →
    vtxPar[i]! < i ∧ ((vtxLab[i]! = 1 ∧ vtxA[vtxPar[i]!]! = i) ∨
      (vtxLab[i]! = 2 ∧ vtxB[vtxPar[i]!]! = i)) := by
  decide +kernel

end CertificateChecks.KernelHSPinned6101

end
