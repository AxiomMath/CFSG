
module

public import Certificates.Kernel.OmegaEight.SB3873GH
public import Certificates.Kernel.OmegaEight.SB3873GW
public import CFSG.Certificates.Kernel.O8.SBClsSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBCenL CFSG.KC.SBCenU CFSG.KC.SBCls

@[expose] noncomputable def clsAtT (k m z : ℕ) (r : ℕ × ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    clsChk (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
      (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens 131072 r

theorem clsAtF_of_T {k m z : ℕ} {r : ℕ × ℕ} (h : clsAtT k m z r = true) :
    clsAtF k m z r = true := by
  unfold clsAtT at h
  unfold clsAtF
  simp only [cen_strictB] at h ⊢
  exact clsChk_imp _ _ _ h

theorem all_clsAt_of_T {k m z : ℕ} {L : List (ℕ × ℕ)} (h : L.all (clsAtT k m z) = true) :
    L.all (clsAt k m z) = true := by
  rw [← clsAtF_eq]
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => clsAtF_of_T (h r hr)

end CertificateChecks.KernelO8.SB3873

end
