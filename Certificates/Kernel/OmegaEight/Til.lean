module

public import CFSG.Certificates.Kernel.O8TilSound
public import Certificates.Kernel.OmegaEight.TilChecks
public import Certificates.Kernel.OmegaEight.T0
public import Certificates.Kernel.OmegaEight.Forms

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.Chain

theorem tilCheck_eq (ε : Eps) : tilCheck ε = tilCheckG (qfB ε) (n0 ε) (genRows ε) (c0Rows ε)
    (uRows ε) (xCode ε) (reflWords ε) (uWords ε) (tilCodes ε) (zTil ε) := by
  unfold tilCheck tilCheckG xCheck xCheckG tabCheck tabCheckG invCheckS invCheckSG
  rw [wordRows_eq, prod4_eq]
  rfl

theorem zCheck_eq (ε : Eps) : zCheck ε = zCheckG (genRows ε) (c0Rows ε) (xCode ε) (uWords ε)
    (tilCodes ε) (tilTree ε) (zTil ε) (zRoot ε) (zAnn ε) (zWit ε) := by
  unfold zCheck zCheckG treeCheck tilGen
  rw [prod4_eq]
  rfl

theorem bindGM : ∀ s < 6, genRows .minus s = decR (mat GMinus s) := by
  intro s hs
  interval_cases s <;> rfl

theorem bindCM : ∀ s < 6, c0Rows .minus s = decR (mat CMinus s) := by
  intro s hs
  interval_cases s <;> rfl

theorem bindTilP : TilBind (tilCodes .plus) TilLP := by
  unfold TilBind
  decide +kernel

theorem bindTilM : TilBind (tilCodes .minus) TilLM := by
  unfold TilBind
  decide +kernel

theorem bindTilXP : dec4 (xCode .plus) = dec4M TilXP := by decide +kernel
theorem bindTilXM : dec4 (xCode .minus) = dec4M TilXM := by decide +kernel

theorem bindTilTrP : ∀ i < 128,
    (tilTree .plus).getD i (0, 0) = (fget TilTRP i 10 % 128, fget TilTRP i 10 / 128) := by
  decide +kernel

theorem bindTilTrM : ∀ i < 128,
    (tilTree .minus).getD i (0, 0) = (fget TilTRM i 10 % 128, fget TilTRM i 10 / 128) := by
  decide +kernel

theorem bindTilWP :
    zWit .plus = TilSWP.map fun x => (x % 4096, x / 4096 % 4096, x / 16777216 == 1) := by
  decide +kernel

theorem bindTilWM :
    zWit .minus = TilSWM.map fun x => (x % 4096, x / 4096 % 4096, x / 16777216 == 1) := by
  decide +kernel

theorem bindTilAP : zAnn .plus = TilZAP.map dig4 := by decide +kernel
theorem bindTilAM : zAnn .minus = TilZAM.map dig4 := by decide +kernel

theorem kXP : xOK QP 12 GPlus CPlus TilXP (reflWords .plus) = true := kXP'
theorem kXM : xOK QM 4 GMinus CMinus TilXM (reflWords .minus) = true := kXM'

theorem cert3497 : tilCheck .plus = true ∧ tilCheck .minus = true := by
  rw [tilCheck_eq, tilCheck_eq]
  exact ⟨til_sound qBind_plus (by decide) bindGP bindCP bindUP bindTilXP bindTilP kXP kTabP
      kTilCloseP kTilInvP,
    til_sound qBind_minus (by decide) bindGM bindCM bindUM bindTilXM bindTilM kXM kTabM
      kTilCloseM kTilInvM⟩

theorem cert3498 : zCheck .plus = true ∧ zCheck .minus = true := by
  rw [zCheck_eq, zCheck_eq]
  exact ⟨z_sound bindGP bindCP bindTilXP bindTilP bindTilTrP bindTilAP bindTilWP kTabP
      kTilCloseP kZP kTilZFinP,
    z_sound bindGM bindCM bindTilXM bindTilM bindTilTrM bindTilAM bindTilWM kTabM kTilCloseM kZM
      kTilZFinM⟩

end CertificateChecks.KernelO8

end
