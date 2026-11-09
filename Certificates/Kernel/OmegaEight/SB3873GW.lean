module

public import Certificates.Kernel.OmegaEight.SB3873GU
public import Certificates.Kernel.OmegaEight.SB3873GH
public import CFSG.Certificates.Kernel.O8.SBCenVSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBCenL CFSG.KC.SBCenU CFSG.KC.SBCenV

@[expose] def sOm : List ℕ := [0, 130, 144, 18, 72, 202, 216, 90]

theorem sActLin : ∀ h < 512, linOK (sActRow h) = true := by decide +kernel

theorem sAct00 : (sActRow 0 >>> 0) &&& 127 = 0 := by decide +kernel

theorem sMt0 : ∀ g < 512, (sMtRow 0 >>> (9 * g)) &&& 511 = g := by decide +kernel

theorem mulK_e128 {e g : ℕ} (he : e < 128) (hg : g < 512) : mulK e (128 * g) = e + 128 * g := by
  have := mul_code (mul := mulK) sActRow sMtRow (fun _ _ _ _ => rfl) he (by norm_num : (0 : ℕ) < 512)
    (by norm_num : (0 : ℕ) < 128) hg
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
  rw [sAct00, Nat.xor_zero, sMt0 g hg] at this
  exact this

@[expose] def CenBW (k m z : ℕ) (Q B : List ℕ) : Prop :=
  (∀ s < 8, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (blkG (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) sActRow sMtRow Q [64, 75] n s)
        (B.getD s 0)) = true) ∧
  ∀ t < 8, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (blkW mulK sActRow sMtRow (rowFN mulK sNfRow W L) z sOm Q [64, 75] n t)
        (B.getD (t + 8) 0)) = true

@[expose] noncomputable def covT (k m : ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    covK (rowFN mulK sNfRow W L) sOm

theorem CenBL_of_W {k m z : ℕ} {Q B : List ℕ} (hz : z < 65536) (hh : homK k m z = true)
    (hc : covT k m = true) (h : CenBW k m z Q B) : CenBL k m z Q B := by
  refine CenBL_of_U hz ⟨h.1, fun t ht => ?_⟩
  have := h.2 t ht
  unfold covT at hc
  simp only [cen_strictB] at this hc ⊢
  have hFN : rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) = FK k m :=
    funext fun x => FK_eqN k m x
  have hFm : ∀ e < 128, ∀ g < 512, rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0)
      (e + 128 * g) = mulK (rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) e)
        (rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) (128 * g)) := by
    intro e he g hg
    rw [hFN, ← mulK_e128 he hg]
    exact homK_mul hh e (by omega) (128 * g) (by omega)
  rw [blkW_eq (mul := mulK) (AR := sActRow) (MR := sMtRow) (fun _ _ _ _ => rfl) (rowFN_lt _ _) hz sActLin
    (by decide) (covK_sound hc) hFm _ _ _ ht] at this
  exact this

end CertificateChecks.KernelO8.SB3873

end
