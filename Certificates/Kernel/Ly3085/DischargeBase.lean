
module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.HN.F5Group
public import Certificates.Kernel.Ly3085.Bridge

@[expose] public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open CertificateChecks.KernelSporSch CFSG.Sporadic.He.Native
open Matrix MulAction

theorem tt_mat [LySeed] :
    LCanon 12 111 111 LySv.TT ∧ bigM LySv.TT = mat lyt := by
  have v1 := LySvF.vVV
  have v2 := LySvF.vVI
  have v3 := LySvF.vTT
  have r := repM_tArr
  unfold tArr vArr at r
  rw [LyBSF.b4_eq, LySvF.v_eq, CFSG.KS.SporSch.LyM.invM_eq Nat.prime_five LyBS.consts
    (LyBSF.hv v1) (LyBSF.hv v2) LySv.vvi, LyBSF.matA_eq, LyBSF.mulE v2 LyBS.vA,
    LyBSF.mulE (LyBSF.mulV v2 LyBS.vA) v1, beq_eq LySv.tt] at r
  exact ⟨canon_vld v3, by rw [bigM_toMat]; exact r⟩

theorem E7_pad (S : Matrix (Fin 7) (Fin 7) (ZMod 5)) :
    E7 * CFSG.KS.LyOm.Pack.padM S * E7ᵀ = S := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨b.val, by omega⟩]
  · rw [Matrix.mul_apply, Finset.sum_eq_single ⟨a.val, by omega⟩]
    · simp [E7, CFSG.KS.LyOm.Pack.padM]
    · intro j _ hj
      have : j.val ≠ a.val := fun e => hj (Fin.ext e)
      simp [E7, this]
    · simp
  · intro j _ hj
    have : j.val ≠ b.val := fun e => hj (Fin.ext e)
    simp [E7, Matrix.transpose_apply, this]
  · simp

theorem el_eq :
    LCanon 12 111 111 CFSG.KD.LyOm.EL ∧ bigM CFSG.KD.LyOm.EL = lyE := by
  have cU : LCanon 12 111 111 LySv.UP := canon_vld LySv.vUP
  obtain ⟨cS, eS⟩ := CFSG.KS.LyOm.Pack.toBig_sound ss_facts.1
  obtain ⟨cT, eT⟩ := SB2.fTr_sound cU
  have cF := vld_mem (X := CFSG.KD.LyOm.FL) (by memL)
  have m1 := fmul cU cS
  have m2 := fmul m1.1 cT
  have m3 := fmul m2.1 cF
  refine ⟨m3.1, ?_⟩
  unfold CFSG.KD.LyOm.EL
  rw [m3.2, m2.2, m1.2, eS, eT, up_eq, ss_facts.2, fl_eq, Matrix.transpose_mul]
  unfold lyE
  calc lyU * E7 * CFSG.KS.LyOm.Pack.padM lySmall * (E7ᵀ * lyUᵀ) * lyF
      = lyU * (E7 * CFSG.KS.LyOm.Pack.padM lySmall * E7ᵀ) * lyUᵀ * lyF := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [E7_pad]

theorem lyt_fix
    [LySeed] : lyt • opE = opE := by
  have h := CFSG.KD.LyOm.fixE
  generalize hB : CFSG.KD.LyOm.BC = b at h
  generalize hE : CFSG.KD.LyOm.EL = e at h
  generalize hT : LySv.TT = t at h
  obtain ⟨-, h2⟩ := bAnd_true h
  subst hB hE hT
  obtain ⟨cE, eE⟩ := el_eq
  obtain ⟨cT, eT⟩ := tt_mat
  have hc : mat lyt * lyE = lyE * mat lyt := by
    rw [← eE, ← eT, ← (fmul cT cE).2, beq_eq h2, (fmul cE cT).2]
  ext1
  rw [LyOperator.smul_val]
  change mat lyt * lyE * mat lyt⁻¹ = lyE
  rw [hc, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]

end CertificateChecks.KernelLy.Omega

end
