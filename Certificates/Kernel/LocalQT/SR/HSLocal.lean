module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.HSLocal
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_sq CFSG.KD.LQT.HS3 CFSG.SectionRank.Native.hsSylow3Data 2 20
  CFSG.Blueprint.NativeSporadic.HSSeed1 CFSG.Blueprint.NativeSporadic.HSSeed2

#lqt_sr_cub CFSG.KD.LQT.HS5 CFSG.SectionRank.Native.hsSylow5Data 2 20
  CFSG.Blueprint.NativeSporadic.HSSeed1 CFSG.Blueprint.NativeSporadic.HSSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.KC.LQT
open scoped commutatorElement

theorem hs_sylow3 :
    ∃ x y h : NativeSporadic.HS,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.HS)) = 3 ^ 2 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 0 ∧ h * y * h⁻¹ = x ^ 2 * y ^ 2 := by
  have h := sq_sound _ CFSG.KD.LQT.HS3.lay_ok CFSG.KD.LQT.HS3.decA CFSG.KD.LQT.HS3.decB
    CFSG.KD.LQT.HS3.one CFSG.KD.LQT.HS3.steps CFSG.KD.LQT.HS3.sq
  rw [← CFSG.KD.LQT.HS3.LA_eq, ← CFSG.KD.LQT.HS3.LB_eq] at h
  exact h

theorem hs_sylow5 :
    ∃ x y h : NativeSporadic.HS,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.HS)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 3 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4 := by
  have h := cub_sound _ CFSG.KD.LQT.HS5.lay_ok CFSG.KD.LQT.HS5.decA CFSG.KD.LQT.HS5.decB
    CFSG.KD.LQT.HS5.one CFSG.KD.LQT.HS5.steps CFSG.KD.LQT.HS5.cub
  rw [← CFSG.KD.LQT.HS5.LA_eq, ← CFSG.KD.LQT.HS5.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
