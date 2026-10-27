
module

public import Certificates.Kernel.Ly3085.Bridge
public import Certificates.Kernel.Ly3085.Omega.SeedRel
public import Certificates.Kernel.Ly3085.Seed
public import Certificates.Kernel.SporSch.Ly.BS18009

public section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Native CFSG.KS.LyOm CertificateChecks.KernelSporSch
open CFSG.Sporadic.He.Native (toMat toMat_powM)
open Matrix

theorem bigM_A : bigM LyBS.A = mA := by
  rw [bigM_toMat, ← LyBSF.matA_eq, toMat_matA]

theorem bigM_B : bigM LyBS.B = mB := by
  rw [bigM_toMat, ← LyBSF.matB_eq, toMat_matB]

theorem bigM_B4 : bigM LyBS.B4 = mB ^ 4 := by
  rw [bigM_toMat, ← LyBSF.b4_eq, toMat_powM, toMat_matB]

theorem cA : LCanon 12 111 111 LyBS.A := canon_vld LyBS.vA

theorem cB : LCanon 12 111 111 LyBS.B := canon_vld LyBS.vB

theorem cB4 : LCanon 12 111 111 LyBS.B4 := canon_vld LyBS.vB4

theorem xs_facts : LCanon 12 111 111 CFSG.KD.LyOm.XS ∧ bigM CFSG.KD.LyOm.XS = mX := by
  have m1 := fmul cB cA
  have m2 := fmul m1.1 m1.1
  have m3 := fmul cA m2.1
  have m4 := fmul m3.1 cB
  have m5 := fmul cA cB4
  have m6 := fmul m5.1 m5.1
  have m7 := fmul m4.1 m6.1
  refine ⟨m7.1, ?_⟩
  unfold CFSG.KD.LyOm.XS
  rw [m7.2, m6.2, m5.2, m4.2, m3.2, m2.2, m1.2, bigM_A, bigM_B, bigM_B4]

theorem xPow_facts : ∀ n : ℕ,
    LCanon 12 111 111 (CFSG.KD.LyOm.xPow n) ∧ bigM (CFSG.KD.LyOm.xPow n) = mX ^ n
  | 0 => by
    refine ⟨one_facts.1, ?_⟩
    rw [pow_zero]
    exact one_facts.2
  | n + 1 => by
    obtain ⟨c, e⟩ := xPow_facts n
    have m := fmul c xs_facts.1
    refine ⟨m.1, ?_⟩
    change bigM (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC (CFSG.KD.LyOm.xPow n) CFSG.KD.LyOm.XS) = _
    rw [m.2, e, xs_facts.2, pow_succ]

theorem form_of {X : ℕ} (hX : LCanon 12 111 111 X)
    (h : Nat.beq (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC (CFSG.KC.LyOm.fMul CFSG.KD.LyOm.BC
      (CFSG.KC.LyOm.fTr X) CFSG.KD.LyOm.FL) X) CFSG.KD.LyOm.FL = true) :
    (bigM X)ᵀ * lyF * bigM X = lyF := by
  have cF := vld_mem (X := CFSG.KD.LyOm.FL) (by memL)
  obtain ⟨cT, eT⟩ := SB2.fTr_sound hX
  have m1 := fmul cT cF
  have m2 := fmul m1.1 hX
  rw [← fl_eq, ← eT, ← m1.2, ← m2.2, beq_eq h]

theorem seedFacts : LySeed where
  mA_sq := by
    have h := CertificateChecks.KernelLy.sA_sq
    rwa [pow_two] at h
  mB_pow := CertificateChecks.KernelLy.sB_pow
  mX_pow := by
    rw [← (xPow_facts 67).2, beq_eq CFSG.KD.LyOm.x67, one_facts.2]
  form_A := by
    have h := form_of cA CFSG.KD.LyOm.formA
    rwa [bigM_A] at h
  form_B := by
    have h := form_of cB CFSG.KD.LyOm.formB
    rwa [bigM_B] at h

end CertificateChecks.KernelLy.Omega

end
