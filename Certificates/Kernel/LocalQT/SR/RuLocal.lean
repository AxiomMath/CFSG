module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.RuLocal
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_cub CFSG.KD.LQT.Ru3 CFSG.SectionRank.Native.ruSylow3Data 2 28
  CFSG.Blueprint.NativeSporadic.RuSeed1 CFSG.Blueprint.NativeSporadic.RuSeed2

#lqt_sr_cub CFSG.KD.LQT.Ru5 CFSG.SectionRank.Native.ruSylow5Data 2 28
  CFSG.Blueprint.NativeSporadic.RuSeed1 CFSG.Blueprint.NativeSporadic.RuSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.KC.LQT
open scoped commutatorElement

theorem ru_sylow3 :
    ∃ x y h : NativeSporadic.Ru,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Ru)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 1 ∧
      h * y * h⁻¹ = x ^ 2 * y ^ 2 * ⁅x, y⁆ ^ 1 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2 := by
  have h := cub_sound _ CFSG.KD.LQT.Ru3.lay_ok CFSG.KD.LQT.Ru3.decA CFSG.KD.LQT.Ru3.decB
    CFSG.KD.LQT.Ru3.one CFSG.KD.LQT.Ru3.steps CFSG.KD.LQT.Ru3.cub
  rw [← CFSG.KD.LQT.Ru3.LA_eq, ← CFSG.KD.LQT.Ru3.LB_eq] at h
  exact h

theorem ru_sylow5 :
    ∃ x y h : NativeSporadic.Ru,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.Ru)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 3 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 3 * ⁅x, y⁆ ^ 4 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4 := by
  have h := cub_sound _ CFSG.KD.LQT.Ru5.lay_ok CFSG.KD.LQT.Ru5.decA CFSG.KD.LQT.Ru5.decB
    CFSG.KD.LQT.Ru5.one CFSG.KD.LQT.Ru5.steps CFSG.KD.LQT.Ru5.cub
  rw [← CFSG.KD.LQT.Ru5.LA_eq, ← CFSG.KD.LQT.Ru5.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
