
module

public import Certificates.Kernel.Sporadic.Fi24Ext.Decoded
import Certificates.Kernel.Sporadic.Fi24Form.Checks
import Certificates.Kernel.Sporadic.Fi24Orb.Small
import CFSG.Certificates.Kernel.Spor.Fi24FormSound

public section

namespace CertificateChecks.KernelFi24Form

open CertificateChecks.KernelFi24Ext CFSG.KC.Fi24FormS Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT CFSG.KD.Fi24Fix.MX
  CFSG.KD.Fi24Ext.M3 CFSG.KD.BrFi24.ONE

theorem mt_A : Mt (CFSG.KD.BrFi24.RB 23) = CFSG.Sporadic.Fi24.mA :=
  A_mt.trans CFSG.Sporadic.Fi24.matW_matA

theorem mt_B : Mt (CFSG.KD.BrFi24.RB 24) = CFSG.Sporadic.Fi24.mB :=
  B_mt.trans CFSG.Sporadic.Fi24.matW_matB

theorem mt_F : Mt CFSG.KD.Fi24Ext.F = CFSG.Sporadic.Fi24.mF := F_mt

theorem cn_F : Cn CFSG.KD.Fi24Ext.F := cn_MX (k := 27) (by norm_num)

theorem A_sq : CFSG.Sporadic.Fi24.mA * CFSG.Sporadic.Fi24.mA = 1 := by
  have e := (mul_mt cn_A cn_A).2
  rw [Nat.eq_of_beq_eq_true CFSG.KD.Fi24Orb.a_sq, mt_one, mt_A] at e
  exact e.symm

theorem B_cube : CFSG.Sporadic.Fi24.mB * (CFSG.Sporadic.Fi24.mB * CFSG.Sporadic.Fi24.mB) = 1 := by
  obtain ⟨c2, e2⟩ := mul_mt cn_B cn_B
  have e := (mul_mt cn_B c2).2
  rw [Nat.eq_of_beq_eq_true CFSG.KD.Fi24Orb.b_cube, mt_one, e2, mt_B] at e
  exact e.symm

theorem F_symm : CFSG.Sporadic.Fi24.mFᵀ = CFSG.Sporadic.Fi24.mF := by
  have h := transM_spec CFSG.KD.Fi24Form.f_sym0 CFSG.KD.Fi24Form.f_sym1 CFSG.KD.Fi24Form.f_sym2
    CFSG.KD.Fi24Form.f_sym3
  change Mt CFSG.KD.Fi24Ext.F = (Mt CFSG.KD.Fi24Ext.F)ᵀ at h
  rw [mt_F] at h
  exact h.symm

theorem form_A :
    CFSG.Sporadic.Fi24.mAᵀ * CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mA = CFSG.Sporadic.Fi24.mF := by
  have h := transM_spec CFSG.KD.Fi24Form.fa_sym0 CFSG.KD.Fi24Form.fa_sym1
    CFSG.KD.Fi24Form.fa_sym2 CFSG.KD.Fi24Form.fa_sym3
  unfold CFSG.KD.Fi24Form.FA at h
  change Mt (CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Ext.F (CFSG.KD.BrFi24.RB 23)) =
    (Mt (CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Ext.F (CFSG.KD.BrFi24.RB 23)))ᵀ at h
  rw [(mul_mt cn_F cn_A).2, mt_F, mt_A] at h
  calc CFSG.Sporadic.Fi24.mAᵀ * CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mA =
        (CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mA)ᵀ * CFSG.Sporadic.Fi24.mA := by
        rw [Matrix.transpose_mul, F_symm]
    _ = CFSG.Sporadic.Fi24.mF * (CFSG.Sporadic.Fi24.mA * CFSG.Sporadic.Fi24.mA) := by
        rw [← h, Matrix.mul_assoc]
    _ = CFSG.Sporadic.Fi24.mF := by rw [A_sq, Matrix.mul_one]

theorem form_B :
    CFSG.Sporadic.Fi24.mBᵀ * CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mB = CFSG.Sporadic.Fi24.mF := by
  have h := transM_spec CFSG.KD.Fi24Form.fb_tr0 CFSG.KD.Fi24Form.fb_tr1
    CFSG.KD.Fi24Form.fb_tr2 CFSG.KD.Fi24Form.fb_tr3
  unfold CFSG.KD.Fi24Form.FBB CFSG.KD.Fi24Form.FB at h
  change Mt (CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Ext.F (CFSG.KD.BrFi24.RB 24)) =
    (Mt (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.MUL CFSG.KD.Fi24Ext.F (CFSG.KD.BrFi24.RB 24))
      (CFSG.KD.BrFi24.RB 24)))ᵀ at h
  obtain ⟨c1, e1⟩ := mul_mt cn_F cn_B
  rw [(mul_mt c1 cn_B).2, e1, mt_F, mt_B] at h
  calc CFSG.Sporadic.Fi24.mBᵀ * CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mB =
        CFSG.Sporadic.Fi24.mBᵀ * (CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mB) := Matrix.mul_assoc _ _ _
    _ = CFSG.Sporadic.Fi24.mBᵀ *
          (CFSG.Sporadic.Fi24.mF * CFSG.Sporadic.Fi24.mB * CFSG.Sporadic.Fi24.mB)ᵀ := by rw [← h]
    _ = (CFSG.Sporadic.Fi24.mB * (CFSG.Sporadic.Fi24.mB * CFSG.Sporadic.Fi24.mB))ᵀ *
          CFSG.Sporadic.Fi24.mFᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = CFSG.Sporadic.Fi24.mF := by rw [B_cube, Matrix.transpose_one, Matrix.one_mul, F_symm]

end CertificateChecks.KernelFi24Form

end
