module

public import CFSG.Sporadic.HN.Commutant
public import Certificates.Data.CFSGNative.HN.Data
public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.J4Hub.BlockSound
public import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.X
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.D
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.O
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.S
import Certificates.Kernel.HN3166.Bytes
import Certificates.Kernel.Sporadic.OrdCommon
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHN

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.F5 CFSG.KD.FamHNSeed

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "OM" =>
  ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HN.Native.hnData) 13 1729

theorem s_mA : mA Dt = OM (RW 1) := by
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide) d1 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedA = _
  rw [CFSG.KD.BrHN.HNSeedA.eq, h]
  rfl

theorem s_mB : mB Dt = OM (RW 2) := by
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide) d2 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedB = _
  rw [CFSG.KD.BrHN.HNSeedB.eq, h]
  rfl

theorem s_v1 : validM 5 229957 L H (RW 1) = true := (andT' (andT' d1_end).2).2

theorem s_v2 : validM 5 229957 L H (RW 2) = true := (andT' (andT' d2_end).2).2

theorem mA_sq : mA Dt ^ 2 = 1 := by
  rw [s_mA]
  exact (ordExact_sound' (hnb := rfl) consts (by norm_num) s_v1 o_A).2.2.1

theorem mB_cube : mB Dt ^ 3 = 1 := by
  rw [s_mB]
  exact (ordExact_sound' (hnb := rfl) consts (by norm_num) s_v2 o_B).2.2.1

theorem det_mA : (mA Dt).det ≠ 0 := det_ne_zero_of_pow_eq_one' (by norm_num) mA_sq

theorem det_mB : (mB Dt).det ≠ 0 := det_ne_zero_of_pow_eq_one' (by norm_num) mB_cube

theorem gA_mem : Matrix.GeneralLinearGroup.mkOfDetNeZero (mA Dt) det_mA ∈ J Dt := by
  have h : gA Dt ∈ J Dt := Subgroup.subset_closure (Set.mem_insert _ _)
  rwa [gA_eq' det_mA] at h

theorem gB_mem : Matrix.GeneralLinearGroup.mkOfDetNeZero (mB Dt) det_mB ∈ J Dt := by
  have h : gB Dt ∈ J Dt := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rwa [gB_eq' det_mB] at h

theorem regs3 : RegsIn 5 (Dt).d 13 1729 229957 L H (J Dt) RW 3 := by
  intro r h0 h3
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨s_v1, _, gA_mem, s_mA⟩
  · exact ⟨s_v2, _, gB_mem, s_mB⟩

theorem regs21 : RegsIn 5 (Dt).d 13 1729 229957 L H (J Dt) RW 21 :=
  slp_sound' (nb := nat_lit 229957) (hnb := rfl) consts regs3 ws (by norm_num)

theorem mat_mul' {D : CFSG.Sporadic.F5.Native.F5Data} (x y : J D) :
    mat D (x * y) = mat D x * mat D y := rfl

theorem mat_pow' {D : CFSG.Sporadic.F5.Native.F5Data} (x : J D) (n : ℕ) :
    mat D (x ^ n) = mat D x ^ n := by
  simp [mat]

theorem mat_one' {D : CFSG.Sporadic.F5.Native.F5Data} : mat D 1 = 1 := rfl

theorem orderOf_x : ∃ g : J Dt, orderOf (a Dt * (g⁻¹ * b Dt * g)) = 19 := by
  obtain ⟨v16, g, hg, eg⟩ := regs21 16 (by norm_num) (by norm_num)
  obtain ⟨v17, -⟩ := regs21 17 (by norm_num) (by norm_num)
  obtain ⟨v18, -⟩ := regs21 18 (by norm_num) (by norm_num)
  obtain ⟨v19, -⟩ := regs21 19 (by norm_num) (by norm_num)
  obtain ⟨v20, -⟩ := regs21 20 (by norm_num) (by norm_num)
  have one : OM ONE = 1 := (one_sound' (hnb := rfl) consts).2
  have hinv : OM (RW 16) * OM (RW 17) = 1 :=
    (mul_sound' (hnb := rfl) consts v16 v17).2.symm.trans
      ((congrArg (ordMat 5 133 13 1729) (Nat.eq_of_beq_eq_true g_inv)).trans one)
  have e18 : OM (RW 18) = OM (RW 1) * OM (RW 17) :=
    (congrArg (ordMat 5 133 13 1729) (Nat.eq_of_beq_eq_true x_18)).trans
      (mul_sound' (hnb := rfl) consts s_v1 v17).2
  have e19 : OM (RW 19) = OM (RW 18) * OM (RW 2) :=
    (congrArg (ordMat 5 133 13 1729) (Nat.eq_of_beq_eq_true x_19)).trans
      (mul_sound' (hnb := rfl) consts v18 s_v2).2
  have e20 : OM (RW 20) = OM (RW 19) * OM (RW 16) :=
    (congrArg (ordMat 5 133 13 1729) (Nat.eq_of_beq_eq_true x_20)).trans
      (mul_sound' (hnb := rfl) consts v19 v16).2
  have ho := ordExact_sound' (hnb := rfl) consts (by norm_num) v20 o_X
  have hp : OM (RW 20) ^ 19 = 1 := ho.2.2.1
  have hne' := ho.2.2.2 19 List.mem_cons_self
  rw [Nat.div_self (by norm_num), pow_one] at hne'
  have hne : OM (RW 20) ≠ 1 := hne'
  let gJ : J Dt := ⟨g, hg⟩
  have hmi : mat Dt gJ⁻¹ = OM (RW 17) := by
    calc mat Dt gJ⁻¹ = mat Dt gJ⁻¹ * (OM (RW 16) * OM (RW 17)) := by rw [hinv, mul_one]
      _ = OM (RW 17) := by
        rw [← eg]
        change ((g⁻¹ : GL (Fin (Dt).d) (ZMod 5)) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5)) *
          ((g : GL (Fin (Dt).d) (ZMod 5)) * OM (RW 17)) = _
        rw [← mul_assoc, Units.inv_mul, one_mul]
  have hmg : mat Dt gJ = OM (RW 16) := eg
  have hx : mat Dt (a Dt * (gJ⁻¹ * b Dt * gJ)) = OM (RW 20) := by
    rw [mat_mul', mat_mul', mat_mul', mat_a' det_mA, mat_b' det_mB, hmi, hmg, s_mA, s_mB, e20,
      e19, e18]
    simp only [mul_assoc]
  refine ⟨gJ, orderOf_eq_prime (hp := ⟨by norm_num⟩) ?_ ?_⟩
  · apply mat_injective Dt
    rw [mat_pow', hx, hp, mat_one']
  · intro h1
    apply hne
    rw [← hx, h1, mat_one']

end CertificateChecks.KernelHN

end
