
module

public import Certificates.Kernel.OmegaEight.SB3873G
public import CFSG.Certificates.Kernel.O8.SBCenFSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF

theorem FK_eqN (k m x : ℕ) :
    rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) x = FK k m x := by
  rw [rowFN_eq]
  exact rowF_eq k m x

@[expose] noncomputable def conjF (k m z a n : ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    (List.range' a n).all fun y =>
      mulK z y == mulK (rowFN mulK sNfRow W L (rowFN mulK sNfRow W L y)) z

theorem conjF_eq (k m z a n : ℕ) : conjF k m z a n = conjOK k m z a n := by
  unfold conjF conjOK
  simp only [cen_strictB, FK_eqN]

@[expose] def CenBF (k m z : ℕ) (Q B : List ℕ) : Prop :=
  ∀ s < 16, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (cenBlk (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) Q [64, 75] n (8192 * s))
        (B.getD s 0)) = true

theorem CenB_of_F {k m z : ℕ} {Q B : List ℕ} (h : CenBF k m z Q B) : CenB k m z Q B := by
  intro s hs
  have := h s hs
  simp only [cen_strictB] at this ⊢
  rw [rowFN_eq] at this
  exact this

end CertificateChecks.KernelO8.SB3873

end
