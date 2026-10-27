module

public import CFSG.Certificates.Kernel.O8OrthSound
public import Certificates.Kernel.OmegaEight.OrthWalk
public import Certificates.Kernel.OmegaEight.OrthChecks

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1
  CFSG.EvenSmallLie.OmegaEight.Chain

theorem gP : ∀ s < 6, genRows .plus s = decR (mat GPlus s) := by
  intro s hs
  interval_cases s <;> rfl
theorem gM : ∀ s < 6, genRows .minus s = decR (mat GMinus s) := by
  intro s hs
  interval_cases s <;> rfl
theorem giP : ∀ s < 6, genInvRows .plus s = decR (mat GIPlus s) := by
  intro s hs
  interval_cases s <;> rfl
theorem giM : ∀ s < 6, genInvRows .minus s = decR (mat GIMinus s) := by
  intro s hs
  interval_cases s <;> rfl

theorem owP : orbitWords .plus = (orbitWords .plus).toList.toArray := by simp
theorem owM : orbitWords .minus = (orbitWords .minus).toList.toArray := by simp
theorem lettersOWP : ∀ w ∈ (orbitWords .plus).toList, ∀ s ∈ w, s < 6 := by decide
theorem lettersOWM : ∀ w ∈ (orbitWords .minus).toList, ∀ s ∈ w, s < 6 := by decide

theorem extendCols_eq (ε : Eps) : extendCols ε = extendColsG (qfB ε) := rfl

theorem oColsAux_eq (ε : Eps) (m : ℕ) (cs : List ℕ) : oColsAux ε m cs = oColsAuxG (qfB ε) m cs := by
  induction m generalizing cs with
  | zero => rfl
  | succ m ih => simp only [oColsAux, oColsAuxG, ih, extendCols_eq]

theorem oCols_eq (ε : Eps) : oCols ε = oColsG (qfB ε) := oColsAux_eq ε 6 []

theorem wordAct_eq (ε : Eps) : wordAct ε = wordActG (genRows ε) := by
  funext w x
  induction w with
  | nil => rfl
  | cons i w ih => simp only [wordAct, wordActG, ih]

theorem genCheck_eq (ε : Eps) : genCheck ε = genCheckG (qfB ε) (genRows ε) (genInvRows ε) := rfl

theorem orbitCheck_eq (ε : Eps) :
    orbitCheck ε = orbitCheckG (qfB ε) (genRows ε) (orbitWords ε) (n0 ε) := by
  unfold orbitCheck orbitCheckG
  rw [wordAct_eq]

theorem dickCheck_eq (ε : Eps) : dickCheck ε = dickCheckG (qfB ε) (genRows ε) (genInvRows ε) := by
  unfold dickCheck dickCheckG
  rw [oCols_eq]

theorem coneCheck_eq (ε : Eps) :
    coneCheck ε = coneCheckG (qfB ε) (coneX ε) (coneXi ε) (coneY ε) (coneYi ε) (coneC ε) := rfl

theorem invCheck_eq (ε : Eps) : invCheck ε = invCheckG (qfB ε) := by
  unfold invCheck invCheckG
  rw [oCols_eq]

theorem oCheck_of {ε : Eps} {Q : Nat} {L : List ℕ} (hq : QBind (qfB ε) Q)
    (h : ∀ c < 64, walkFrom Q (fun _ => 1) c = L.getD c 0) (hl : L.length ≤ 64)
    (hs : L.sum = oBound ε) : oCheck ε = true := by
  rw [oCheck, oCols_eq, oCount_eq hq h hl, hs]
  exact beq_self_eq_true _

theorem cert3370 : (genCheck .plus = true) ∧ (genCheck .minus = true) ∧ (orbitCheck .plus = true)
    ∧ (orbitCheck .minus = true) ∧ (oCheck .plus = true) ∧ (oCheck .minus = true)
    ∧ (dickCheck .plus = true) ∧ (dickCheck .minus = true) ∧ (coneCheck .plus = true)
    ∧ (coneCheck .minus = true) := by
  have g1 := gen_sound qBind_plus gP giP kGenP
  have g2 := gen_sound qBind_minus gM giM kGenM
  rw [genCheck_eq, genCheck_eq, orbitCheck_eq, orbitCheck_eq, dickCheck_eq, dickCheck_eq,
    coneCheck_eq, coneCheck_eq]
  refine ⟨g1, g2, orbit_sound qBind_plus gP owP lettersOWP kOrbP,
    orbit_sound qBind_minus gM owM lettersOWM kOrbM,
    oCheck_of qBind_plus kCntP (by decide) (by decide),
    oCheck_of qBind_minus kCntM (by decide) (by decide),
    dick_sound qBind_plus kFormP gP giP g1 kDickP,
    dick_sound qBind_minus kFormM gM giM g2 kDickM, ?_, ?_⟩
  · exact cone_sound qBind_plus rfl rfl rfl rfl (by decide) rfl kConeP
  · exact cone_sound qBind_minus rfl rfl rfl rfl (by decide) rfl kConeM

theorem cert3491 : (invCheck .plus = true) ∧ (invCheck .minus = true) := by
  rw [invCheck_eq, invCheck_eq]
  exact ⟨inv_sound qBind_plus kInvP, inv_sound qBind_minus kInvM⟩

end CertificateChecks.KernelO8

end
