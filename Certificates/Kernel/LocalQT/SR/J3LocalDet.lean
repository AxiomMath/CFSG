module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.J3LocalDet
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_locdet CFSG.KD.LQT.J3L CFSG.SectionRank.Native.j3LocDetData 2 80
  CFSG.Blueprint.NativeSporadic.J3Seed1 CFSG.Blueprint.NativeSporadic.J3Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem fac360 : (360 : ℕ).factorization 3 = 2 := by
  rw [show (360 : ℕ) = 3 ^ 2 * 40 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem j3_local_det :
    ∃ (K : Subgroup NativeSporadic.J3) (_ : Group.IsPerfect K) (Q : Sylow 3 K) (x y : K)
      (h k : NativeSporadic.J3),
      Nat.card K = 360 ∧ IsElemAbelian 3 (Q : Subgroup K) ∧
      Nat.card (Q : Subgroup K) = 3 ^ 2 ∧
      h ∈ Subgroup.normalizer (K : Set NativeSporadic.J3) ∧
      Subgroup.closure ({x, y} : Set K) = Q ∧
      h * x * h⁻¹ = (x : NativeSporadic.J3) ^ 2 * (y : NativeSporadic.J3) ^ 1 ∧
      h * y * h⁻¹ = (x : NativeSporadic.J3) ^ 1 * (y : NativeSporadic.J3) ^ 0 ∧
      (∀ g ∈ K, Commute k g) ∧ orderOf k = 3 ∧ Subgroup.zpowers k ⊓ K = ⊥ := by
  have h := loc_sound _ CFSG.KD.LQT.J3L.lay_ok CFSG.KD.LQT.J3L.decA CFSG.KD.LQT.J3L.decB
    CFSG.KD.LQT.J3L.one CFSG.KD.LQT.J3L.steps fac360 CFSG.KD.LQT.J3L.loc
  rw [← CFSG.KD.LQT.J3L.LA_eq, ← CFSG.KD.LQT.J3L.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
