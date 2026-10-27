module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.HeLocal
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_cub CFSG.KD.LQT.He3 CFSG.SectionRank.Native.heSylow3Data 7 50
  CFSG.Blueprint.NativeSporadic.HeSeed1 CFSG.Blueprint.NativeSporadic.HeSeed2

#lqt_sr_sq CFSG.KD.LQT.He5 CFSG.SectionRank.Native.heSylow5Data 7 50
  CFSG.Blueprint.NativeSporadic.HeSeed1 CFSG.Blueprint.NativeSporadic.HeSeed2

#lqt_sr_cub CFSG.KD.LQT.He7 CFSG.SectionRank.Native.heSylow7Data 7 50
  CFSG.Blueprint.NativeSporadic.HeSeed1 CFSG.Blueprint.NativeSporadic.HeSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.KC.LQT
open scoped commutatorElement

theorem he_sylow3 :
    ∃ x y h : NativeSporadic.He,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.He)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 := by
  have h := cub_sound _ CFSG.KD.LQT.He3.lay_ok CFSG.KD.LQT.He3.decA CFSG.KD.LQT.He3.decB
    CFSG.KD.LQT.He3.one CFSG.KD.LQT.He3.steps CFSG.KD.LQT.He3.cub
  rw [← CFSG.KD.LQT.He3.LA_eq, ← CFSG.KD.LQT.He3.LB_eq] at h
  exact h

theorem he_sylow5 :
    ∃ x y h : NativeSporadic.He,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.He)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 4 ∧ h * y * h⁻¹ = x ^ 4 * y ^ 0 := by
  have h := sq_sound _ CFSG.KD.LQT.He5.lay_ok CFSG.KD.LQT.He5.decA CFSG.KD.LQT.He5.decB
    CFSG.KD.LQT.He5.one CFSG.KD.LQT.He5.steps CFSG.KD.LQT.He5.sq
  rw [← CFSG.KD.LQT.He5.LA_eq, ← CFSG.KD.LQT.He5.LB_eq] at h
  exact h

theorem he_sylow7 :
    ∃ x y h : NativeSporadic.He,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.He)) = 7 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 3 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2 := by
  have h := cub_sound _ CFSG.KD.LQT.He7.lay_ok CFSG.KD.LQT.He7.decA CFSG.KD.LQT.He7.decB
    CFSG.KD.LQT.He7.one CFSG.KD.LQT.He7.steps CFSG.KD.LQT.He7.cub
  rw [← CFSG.KD.LQT.He7.LA_eq, ← CFSG.KD.LQT.He7.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
