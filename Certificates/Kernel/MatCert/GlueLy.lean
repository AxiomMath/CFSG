module

public import Certificates.Kernel.MatCert.Ly
public import Certificates.Kernel.SporSch.Ly.Seven2189
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsFpKSound
public import CFSG.Certificates.Kernel.SporSch.LySevenSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveDefs
public import CFSG.Certificates.Kernel.Spor.Loops
import all CFSG.Blueprint.NativeSporadic
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.Ord CFSG.KD.OrdLy CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch
open CFSG.KS (allN_spec)

noncomputable abbrev HL : Hom (opsP 5 111) OL := homP LyBS.consts (by norm_num)

theorem lyA : (opsP 5 111).decode NativeSporadic.LySeed1 = HL.U LyBS.A := LyBSF.matA_eq

theorem lyB : (opsP 5 111).decode NativeSporadic.LySeed2 = HL.U LyBS.B := LyBSF.matB_eq

theorem vldL {X : Nat} (h : LyBS.vld X = true) : HL.P X := h

theorem lyThree : lyCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
    (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 0))
    (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 1)) lyThreeN lyThreeProg
    lyTzSpec lyCzSpec = true := by
  have hp : lyThreeProg.all (Op.lt lyThreeN) = true := by decide +kernel
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N HL lyA lyB (vldL LyBS.vA) (vldL LyBS.vB) hp ly3_K
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨hc, h0⟩, h1⟩, hr0⟩, hr1⟩, hc0⟩, hc1⟩ := hk
  have e0 : seedWord 0 = seedWord0 := rfl
  have e1 : seedWord 1 = seedWord1 := rfl
  have w0 := allN_spec LyBS.vCF 0 (by norm_num)
  have w1 := allN_spec LyBS.vCF 1 (by norm_num)
  beta_reduce at w0 w1
  have vc0 : LyBS.vld (LyBS.CF 0) = true := (LyBSF.andOf w0).1
  have vc1 : LyBS.vld (LyBS.CF 1) = true := (LyBSF.andOf w1).1
  have q0 : (opsP 5 111).eq ((opsP 5 111).regsOf NativeSporadic.LySeed1 NativeSporadic.LySeed2
      lyThreeN lyThreeProg)[lyTzSpec.gen.rc0]! (CFSG.KS.SporSch.LyM.unpackL 111 12 1332 (LyBS.CF 0)) =
      OL.eq (getN Rl lyTzSpec.gen.rc0) (LyBS.CF 0) :=
    eq_of_rel HL hR (by rw [hlen]; exact hr0) (vldL vc0)
  have q1 : (opsP 5 111).eq ((opsP 5 111).regsOf NativeSporadic.LySeed1 NativeSporadic.LySeed2
      lyThreeN lyThreeProg)[lyTzSpec.gen.rc1]! (CFSG.KS.SporSch.LyM.unpackL 111 12 1332 (LyBS.CF 1)) =
      OL.eq (getN Rl lyTzSpec.gen.rc1) (LyBS.CF 1) :=
    eq_of_rel HL hR (by rw [hlen]; exact hr1) (vldL vc1)
  rw [e0, e1, LyBSF.b4_eq, LyBSF.c0_eq, LyBSF.c1_eq]
  unfold lyCheck certOK
  simp only
  rw [lyA, lyB,
    eq_of_rel HL hR (by rw [hlen]; decide) (vldL LyBS.vA),
    eq_of_rel HL hR (by rw [hlen]; decide) (vldL LyBS.vB), q0, q1,
    facts_of_rel HL hR hlen, h0, h1, hc0, hc1]
  unfold certN at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, and_true, true_and] at hc ⊢
  exact ⟨hc.1, hc.2.1, hc.2.2, by decide +kernel⟩

theorem lyFive : ly5Check (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
    [(pairAt (aStarArr (powM 5 111 matB 4)) 2).1, (pairAt (aStarArr (powM 5 111 matB 4)) 3).1,
      (pairAt (aStarArr (powM 5 111 matB 4)) 4).1, (pairAt (aStarArr (powM 5 111 matB 4)) 5).1,
      (pairAt (aStarArr (powM 5 111 matB 4)) 6).1] (fun X => !stabOK X) lyFiveN lyFiveProg
    lyTzSpec5 lyCzSpec5 = true := by
  have hp : lyFiveProg.all (Op.lt lyFiveN) = true := by decide +kernel
  obtain ⟨Rl, hk, hlen, hR⟩ := regs_of_N HL lyA lyB (vldL LyBS.vA) (vldL LyBS.vB) hp ly5_K
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨hc, h0⟩, h1⟩, hels⟩, hrs⟩, hst⟩ := hk
  have vAF : ∀ j < 7, LyBS.vld (LySv.AF j) = true := by
    intro j hj
    have w := allN_spec LySv.vAF j hj
    beta_reduce at w
    exact (LyBSF.andOf w).1
  have hels' : (List.range 5).all (fun j =>
      (opsP 5 111).eq ((opsP 5 111).regsOf NativeSporadic.LySeed1 NativeSporadic.LySeed2 lyFiveN
          lyFiveProg)[(lyTzSpec5.gen.els.getD j default).reg]!
        ([HL.U (LySv.AF 2), HL.U (LySv.AF 3), HL.U (LySv.AF 4), HL.U (LySv.AF 5),
          HL.U (LySv.AF 6)].getD j default)) = true := by
    rw [List.all_eq_true] at hels ⊢
    intro j hj
    have hj5 := List.mem_range.1 hj
    have h := hels j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have eg : [HL.U (LySv.AF 2), HL.U (LySv.AF 3), HL.U (LySv.AF 4), HL.U (LySv.AF 5),
        HL.U (LySv.AF 6)].getD j default = HL.U (LySv.AF (j + 2)) := by
      interval_cases j <;> rfl
    rw [eg, eq_of_rel HL hR (by rw [hlen]; exact h.1) (vldL (vAF (j + 2) (by omega)))]
    exact h.2
  have hX := hR.2 lyTzSpec5.gen.rs (by rw [hlen]; exact hrs)
  have hstab : (!stabOK ((opsP 5 111).regsOf NativeSporadic.LySeed1 NativeSporadic.LySeed2 lyFiveN
      lyFiveProg)[lyTzSpec5.gen.rs]!) = true := by
    rw [hX.1]
    change (!stabOK (CFSG.KS.SporSch.LyM.unpackL 111 12 1332 (getN Rl lyTzSpec5.gen.rs))) = true
    rw [CFSG.KS.SporSch.LySev.stab_eq LyBS.consts hX.2 LySv.vUP LySvF.up_eq]
    exact hst
  rw [LyBSF.b4_eq, LySvF.asF (j := 2) (by norm_num), LySvF.asF (j := 3) (by norm_num),
    LySvF.asF (j := 4) (by norm_num), LySvF.asF (j := 5) (by norm_num),
    LySvF.asF (j := 6) (by norm_num)]
  unfold ly5Check certOK
  simp only
  rw [lyA, lyB,
    eq_of_rel HL hR (by rw [hlen]; decide) (vldL LyBS.vA),
    eq_of_rel HL hR (by rw [hlen]; decide) (vldL LyBS.vB), facts_of_rel HL hR hlen, h0, h1]
  unfold certN at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, and_true, true_and] at hc ⊢
  exact ⟨hc.1, hc.2.1, hc.2.2, by decide, by decide, hels', hstab, rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end CertificateChecks.KernelMC

end
