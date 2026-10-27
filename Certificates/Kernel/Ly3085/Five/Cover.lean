
module

public import Certificates.Kernel.Ly3085.Five.CoverBase

public import Certificates.Kernel.Ly3085.Five.Glue
public import Certificates.Kernel.Ly3085.Five.Checks
public import Certificates.Kernel.LyFiveL1.Tree0
public import Certificates.Kernel.LyFiveL1.Tree1
public import Certificates.Kernel.LyFiveL1.Tree2
public import Certificates.Kernel.LyFiveL1.Tree3
public import Certificates.Kernel.LyFiveL1.Base
public import Certificates.Kernel.Ly3085.Squeeze
public import CFSG.Certificates.Kernel.Common.ForallChunks

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega CFSG.RankThree.Native
  CFSG.RankThree.PartOne.LyFive CFSG.KS.LyOm MulAction
open CFSG.KC.LyFive (wordF powF pow5F elF elW edgeF recF posF abL hL)
open CertificateChecks.KernelSporSch
open Matrix

set_option maxRecDepth 400000

section

variable [LySeed]

theorem tr_mem {t : List ℤ} (ht : ∀ z ∈ t, z = 1 ∨ z = 2) {W : ℕ} {w : J}
    (cW : LCanon 12 111 111 W) (eW : bigM W = mat w) (h : CFSG.KD.LyFive.trOK t W = true) :
    (evalWord seedFam t)⁻¹ * w * evalWord seedFam t ∈ lyH := by
  unfold CFSG.KD.LyFive.trOK at h
  rw [CFSG.KS.LyFive.letB_eq] at h
  obtain ⟨e1, e2⟩ := evalWord_eq ht
  have lt1 : ∀ l ∈ t.map abL, l < 4 := fun l hl => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hl
    exact abL_lt z
  have lt2 : ∀ l ∈ (t.reverse.map abL).map fun l => (l + 2) % 4, l < 4 := fun l hl => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hl
    exact Nat.mod_lt _ (by norm_num)
  obtain ⟨cT, eT⟩ := gab_word' _ lt1
  obtain ⟨cTI, eTI⟩ := gab_word' _ lt2
  rw [← e1] at eT
  rw [← e2] at eTI
  have m1 := fmul cTI cW
  have m2 := fmul m1.1 cT
  rw [m1.2, eTI, eW, eT, ← mat_mul, ← mat_mul] at m2
  set z := (evalWord seedFam t)⁻¹ * w * evalWord seedFam t
  have hE := el_eq
  have m3 := fmul m2.1 hE.1
  have m4 := fmul hE.1 m2.1
  have hc : mat z * CFSG.Sporadic.LySchreier.lyE = CFSG.Sporadic.LySchreier.lyE * mat z := by
    rw [← m2.2, ← hE.2, ← m3.2, ← m4.2, CFSG.KS.LyFive.beq_eq h]
  rw [← F1.1, mem_stabilizer_iff]
  apply LyOperator.ext
  rw [LyOperator.smul_val]
  change mat z * CFSG.Sporadic.LySchreier.lyE * mat z⁻¹ = CFSG.Sporadic.LySchreier.lyE
  rw [hc, Matrix.mul_assoc, ← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]

theorem tr_x : (evalWord seedFam xWord)⁻¹ * fiveX * evalWord seedFam xWord ∈ lyH :=
  tr_mem words_12.1 x_facts.1 x_facts.2 CFSG.KD.LyFive.trX

theorem tr_y3 : (evalWord seedFam y3Word)⁻¹ * fiveY * evalWord seedFam y3Word ∈ lyH :=
  tr_mem words_12.2.1 y_facts.1 y_facts.2 CFSG.KD.LyFive.trY3

theorem tr_y1 : (evalWord seedFam y1Word)⁻¹ * fiveY * evalWord seedFam y1Word ∈ lyH :=
  tr_mem words_12.2.2 y_facts.1 y_facts.2 CFSG.KD.LyFive.trY1

theorem fiveFacts_of : LyFiveFacts := by
  refine ⟨tr_x, tr_y3, tr_y1, conj_tA, conj_tB, fun n hn h1 h5 => ?_⟩
  by_cases hpos : posF CFSG.KD.LyFive.PB n = 16383
  · exact absurd h5 (not_pow5 hn hpos h1)
  · obtain ⟨-, hq⟩ := CFSG.KS.LyFive.posOK_sound CFSG.KD.LyFive.pos n hn
    obtain ⟨hlt, ho⟩ := hq hpos
    have h := (tree_rel _ hlt).2
    rw [ho] at h
    exact h

end

end CertificateChecks.KernelLy.Omega

end
