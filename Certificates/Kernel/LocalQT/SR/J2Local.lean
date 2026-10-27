module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.J2Local
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_cub CFSG.KD.LQT.J23 CFSG.SectionRank.Native.j2Sylow3Data 5 14
  CFSG.Blueprint.NativeSporadic.J2Seed1 CFSG.Blueprint.NativeSporadic.J2Seed2

#lqt_sr_sq CFSG.KD.LQT.J25 CFSG.SectionRank.Native.j2Sylow5Data 5 14
  CFSG.Blueprint.NativeSporadic.J2Seed1 CFSG.Blueprint.NativeSporadic.J2Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.KC.LQT
open scoped commutatorElement

theorem j2_sylow3 :
    ∃ x y h : NativeSporadic.J2,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.J2)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 2 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2 := by
  have h := cub_sound _ CFSG.KD.LQT.J23.lay_ok CFSG.KD.LQT.J23.decA CFSG.KD.LQT.J23.decB
    CFSG.KD.LQT.J23.one CFSG.KD.LQT.J23.steps CFSG.KD.LQT.J23.cub
  rw [← CFSG.KD.LQT.J23.LA_eq, ← CFSG.KD.LQT.J23.LB_eq] at h
  exact h

theorem j2_sylow5 :
    ∃ x y h : NativeSporadic.J2,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.J2)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 4 ∧ h * y * h⁻¹ = x ^ 4 * y ^ 0 := by
  have h := sq_sound _ CFSG.KD.LQT.J25.lay_ok CFSG.KD.LQT.J25.decA CFSG.KD.LQT.J25.decB
    CFSG.KD.LQT.J25.one CFSG.KD.LQT.J25.steps CFSG.KD.LQT.J25.sq
  rw [← CFSG.KD.LQT.J25.LA_eq, ← CFSG.KD.LQT.J25.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
