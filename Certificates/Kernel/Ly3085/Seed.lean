module

public import CFSG.Sporadic.Ly.SeedGroup
public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.J4Hub.BlockSound
public import CFSG.Certificates.Kernel.Fam.LySeed.Checks.X
import CFSG.Certificates.Kernel.Fam.LySeed.Checks.D
import CFSG.Certificates.Kernel.Fam.LySeed.Checks.K
import CFSG.Certificates.Kernel.Fam.LySeed.Checks.O
import CFSG.Certificates.Kernel.Fam.LySeed.Checks.S
import Certificates.Kernel.Ly3085.Bytes
import Certificates.Kernel.Sporadic.OrdCommon
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.Ly CFSG.KD.FamLySeed

local notation "OM" => ordMat 5 111 12 1332

theorem s_mA : sA = OM (RW 1) := by
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide) d1 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed1 = _
  rw [CFSG.KD.BrLy.LySeedA.eq, h]

theorem s_mB : sB = OM (RW 2) := by
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide) d2 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed2 = _
  rw [CFSG.KD.BrLy.LySeedB.eq, h]

theorem s_v1 : validM 5 147852 L H (RW 1) = true := (andT' (andT' d1_end).2).2

theorem s_v2 : validM 5 147852 L H (RW 2) = true := (andT' (andT' d2_end).2).2

theorem sA_sq : sA ^ 2 = 1 := by
  rw [s_mA]
  exact (ordExact_sound' (hnb := rfl) consts (by norm_num) s_v1 o_A).2.2.1

theorem sB_pow : sB ^ 5 = 1 := by
  rw [s_mB]
  exact (ordExact_sound' (hnb := rfl) consts (by norm_num) s_v2 o_B).2.2.1

theorem det_sA : sA.det ≠ 0 := CFSG.Sporadic.F5.det_ne_zero_of_pow_eq_one' (by norm_num) sA_sq

theorem det_sB : sB.det ≠ 0 := CFSG.Sporadic.F5.det_ne_zero_of_pow_eq_one' (by norm_num) sB_pow

theorem regs3 : RegsIn 5 111 12 1332 147852 L H JS RW 3 := by
  intro r h0 h3
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact ⟨s_v1, _, (aS det_sA).2, s_mA⟩
  · exact ⟨s_v2, _, (bS det_sB).2, s_mB⟩

theorem regs19 : RegsIn 5 111 12 1332 147852 L H JS RW 19 :=
  slp_sound' (nb := nat_lit 147852) (hnb := rfl) consts regs3 ws (by norm_num)

theorem orderOf_x : ∃ g : JS, orderOf (aS det_sA * (g⁻¹ * bS det_sB * g)) = 67 := by
  obtain ⟨v14, g, hg, eg⟩ := regs19 14 (by norm_num) (by norm_num)
  obtain ⟨v15, -⟩ := regs19 15 (by norm_num) (by norm_num)
  obtain ⟨v16, -⟩ := regs19 16 (by norm_num) (by norm_num)
  obtain ⟨v17, -⟩ := regs19 17 (by norm_num) (by norm_num)
  obtain ⟨v18, -⟩ := regs19 18 (by norm_num) (by norm_num)
  have one : OM ONE = 1 := (one_sound' (hnb := rfl) consts).2
  have hinv : OM (RW 14) * OM (RW 15) = 1 :=
    (mul_sound' (hnb := rfl) consts v14 v15).2.symm.trans
      ((congrArg OM (Nat.eq_of_beq_eq_true g_inv)).trans one)
  have e16 : OM (RW 16) = OM (RW 1) * OM (RW 15) :=
    (congrArg OM (Nat.eq_of_beq_eq_true x_16)).trans (mul_sound' (hnb := rfl) consts s_v1 v15).2
  have e17 : OM (RW 17) = OM (RW 16) * OM (RW 2) :=
    (congrArg OM (Nat.eq_of_beq_eq_true x_17)).trans (mul_sound' (hnb := rfl) consts v16 s_v2).2
  have e18 : OM (RW 18) = OM (RW 17) * OM (RW 14) :=
    (congrArg OM (Nat.eq_of_beq_eq_true x_18)).trans (mul_sound' (hnb := rfl) consts v17 v14).2
  have ho := ordExact_sound' (hnb := rfl) consts (by norm_num) v18 o_x
  have hp : OM (RW 18) ^ 67 = 1 := ho.2.2.1
  have hne' := ho.2.2.2 67 List.mem_cons_self
  rw [Nat.div_self (by norm_num), pow_one] at hne'
  have hne : OM (RW 18) ≠ 1 := hne'
  let gJ : JS := ⟨g, hg⟩
  have hmi : matS gJ⁻¹ = OM (RW 15) := by
    calc matS gJ⁻¹ = matS gJ⁻¹ * (OM (RW 14) * OM (RW 15)) := by rw [hinv, Matrix.mul_one]
      _ = OM (RW 15) := by
        rw [← eg]
        change ((g⁻¹ : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5)) *
          ((g : GL (Fin 111) (ZMod 5)) * OM (RW 15)) = _
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hmg : matS gJ = OM (RW 14) := eg
  have hx : matS (aS det_sA * (gJ⁻¹ * bS det_sB * gJ)) = OM (RW 18) := by
    rw [matS_mul, matS_mul, matS_mul, matS_aS, matS_bS, hmi, hmg, s_mA, s_mB, e18, e17, e16]
    simp only [Matrix.mul_assoc]
  refine ⟨gJ, orderOf_eq_prime (hp := ⟨by norm_num⟩) ?_ ?_⟩
  · apply matS_injective
    rw [matS_pow, hx, hp, matS_one]
  · intro h1
    apply hne
    rw [← hx, h1, matS_one]

end CertificateChecks.KernelLy

end
