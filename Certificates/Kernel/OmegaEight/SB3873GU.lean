
module

public import Certificates.Kernel.OmegaEight.SB3873GL
public import CFSG.Certificates.Kernel.O8.SBCenUSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBCenL CFSG.KC.SBCenU

theorem rowFN_lt (W L : ℕ) : ∀ a < 65536, rowFN mulK sNfRow W L a < 65536 := by
  intro a _
  unfold rowFN
  simp only [cen_nIf, cen_strictN]
  split <;> exact mulK_lt _ _

@[expose] noncomputable def conjU (k m z a : ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    conjB mulK (rowFN mulK sNfRow W L) z a 8192

theorem conjOK_of_U {k m z a : ℕ} (h : conjU k m z a = true) : conjOK k m z a 8192 = true := by
  unfold conjU at h
  simp only [cen_strictB] at h
  have hc := conjB_sound h
  unfold conjOK
  rw [List.all_eq_true]
  intro y hy
  rw [List.mem_range'_1] at hy
  have := hc (y - a) (by omega)
  rw [Nat.add_sub_cancel' hy.1, FK_eqN, FK_eqN] at this
  exact beq_iff_eq.2 this

@[expose] def CenBU (k m z : ℕ) (Q B : List ℕ) : Prop :=
  (∀ s < 8, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (blkG (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) sActRow sMtRow Q [64, 75] n s)
        (B.getD s 0)) = true) ∧
  ∀ t < 8, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    strictB Q.length fun n =>
      Nat.beq (blkU mulK sActRow sMtRow (rowFN mulK sNfRow W L) z Q [64, 75] n t)
        (B.getD (t + 8) 0)) = true

theorem CenBL_of_U {k m z : ℕ} {Q B : List ℕ} (hz : z < 65536) (h : CenBU k m z Q B) :
    CenBL k m z Q B := by
  refine ⟨h.1, fun s hs1 hs2 => ?_⟩
  have := h.2 (s - 8) (by omega)
  simp only [cen_strictB] at this ⊢
  rw [blkU_eq (mul := mulK) (AR := sActRow) (MR := sMtRow) (fun _ _ _ _ => rfl) (rowFN_lt _ _) hz
    (by decide) _ (by omega : s - 8 < 8), show s - 8 + 8 = s by omega] at this
  exact this

end CertificateChecks.KernelO8.SB3873

end
