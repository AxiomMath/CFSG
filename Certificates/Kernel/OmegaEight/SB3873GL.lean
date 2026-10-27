
module

public import Certificates.Kernel.OmegaEight.SB3873GK
public import Certificates.Kernel.OmegaEight.SB3873L
public import CFSG.Certificates.Kernel.O8.SBCenLSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBCenL

theorem sqFacts : ∀ g < 512, SqAt sActRow sMtRow g :=
  sqFacts_of_blk fun b hb =>
    match b, hb with
    | 0, _ => sqBlk0
    | 1, _ => sqBlk1
    | 2, _ => sqBlk2
    | 3, _ => sqBlk3
    | 4, _ => sqBlk4
    | 5, _ => sqBlk5
    | 6, _ => sqBlk6
    | 7, _ => sqBlk7
    | n + 8, h => absurd h (by omega)

theorem mulK_low (F : ℕ → ℕ) (z : ℕ) :
    ∀ c d, c < 65536 → d < 65536 → extMulF 65536 mulK F z c d = sMulG sActRow sMtRow c d := by
  intro c d hc hd
  unfold extMulF
  simp only [cen_nIf, cen_blt, decide_eq_true_eq, hc, hd, ↓reduceIte]
  rfl

@[expose] def CenBL (k m z : ℕ) (Q B : List ℕ) : Prop :=
  (∀ s < 8, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (blkG (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) sActRow sMtRow Q [64, 75] n s)
        (B.getD s 0)) = true) ∧
  ∀ s, 8 ≤ s → s < 16 → (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (cenBlk (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) Q [64, 75] n (8192 * s))
        (B.getD s 0)) = true

theorem CenBF_of_L {k m z : ℕ} {Q B : List ℕ} (h : CenBL k m z Q B) : CenBF k m z Q B := by
  intro s hs
  by_cases h8 : s < 8
  · have := h.1 s h8
    simp only [cen_strictB] at this ⊢
    rw [blk_eq (mulK_low _ _) sqFacts (by decide) _ h8] at this
    exact this
  · exact h.2 s (by omega) hs

end CertificateChecks.KernelO8.SB3873

end
