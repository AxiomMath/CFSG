module

public import Certificates.Kernel.OmegaEight.N3MW
public import Certificates.Kernel.OmegaEight.PnSWEq
public import CFSG.Certificates.Kernel.O8N3Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.O8CentOrbSound
import CFSG.Certificates.Kernel.O8ColFixSound
import CFSG.Certificates.Kernel.O8ParFixSound
import Certificates.Kernel.OmegaEight.N3MCentS
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

set_option maxHeartbeats 0 in
theorem s0_okN3M : sChk0 wN3M = true := by
  have hS : sortedK (decE EnN3MS0.D EnN3MS0.m).keys = true := (Enum.of_enumOK sE0_okN3M).2.1
  have hM : sortedK (decE EnN3MM0.D EnN3MM0.m).keys = true := (Enum.of_enumOK mE0_okN3M).2.1
  simp only [sChk0, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE0_okN3M⟩, ?_⟩, ?_⟩, ?_⟩, mE0_okN3M⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Minus.base,
      N3Split.Minus.cGens, N3Split.Minus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [gensOK, N3Split.Minus.sGens0, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq,
      idK_eq, ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens, N3Split.Minus.tGens,
      splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Minus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [mulK_sq_bne (j := 10) (by norm_num)]
      simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB_eq_P]
      refine all_range_of_blocks (m := EnN3MS0.m) (s := 9) (nb := 32) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Minus.sReps0, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3M, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | rfl
      iterate 2
        right
        decide +kernel
      all_goals left
      · exact candB_false_of_cent sE0_okN3M (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs0N3M.getD 2 []) (centKs0N3M.getD 2 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_sixteen_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · exact candB_false_of_cent sE0_okN3M (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs0N3M.getD 3 []) (centKs0N3M.getD 3 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_sixteen_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · exact candB_false_of_cent sE0_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs0N3M.getD 4 []) (centKs0N3M.getD 4 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3M, memK_decE_eq hM (by decide +kernel)]
    quickRfl

set_option maxHeartbeats 0 in
theorem tau0_okN3M : tauChk0 wN3M = true := by
  have hS : sortedK (decE EnN3MS0.D EnN3MS0.m).keys = true := (Enum.of_enumOK sE0_okN3M).2.1
  have hfc : fixCount N3Split.Minus.tauK = 64 := by
    rw [fixCount_eq_P]
    decide +kernel
  have hB : fixLB N3Split.Minus.tauK [1024, 256, 96, 16, 4, 1] = true := by
    rw [fixLB_eq_P]
    decide +kernel
  obtain ⟨hcc, hko⟩ := commKer_of_orb (s := N3Split.Minus.tauK) sE0_okN3M
    (centTs0N3M.getD 5 []) (centKs0N3M.getD 5 [])
    (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel) (by decide +kernel)
    (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel) (by decide +kernel)
    (by simp only [wN3M, decE_keys_size]; decide +kernel)
  simp only [tauChk0, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, hfc⟩, ?_⟩, ?_⟩
  · simp only [wN3M, memK_decE_eq hS (by decide +kernel)]
    quickRfl
  · rw [hcc]
    decide +kernel
  · rw [kerCount, hko]
    simp only [fixesOn_fixVecs_basis hB hfc, fixesOn_P (vs := [1024, 256, 96, 16, 4, 1]) (by decide),
      wN3M, decE_getD]
    decide +kernel
  · simp only [invPair, mulK_eq, idK_eq]
    quickRfl

set_option maxHeartbeats 0 in
theorem s1_okN3M : sChk1 wN3M = true := by
  have hS : sortedK (decE EnN3MS1.D EnN3MS1.m).keys = true := (Enum.of_enumOK sE1_okN3M).2.1
  have hM : sortedK (decE EnN3MM1.D EnN3MM1.m).keys = true := (Enum.of_enumOK mE1_okN3M).2.1
  simp only [sChk1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE1_okN3M⟩, ?_⟩, ?_⟩, ?_⟩, mE1_okN3M⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Minus.base,
      N3Split.Minus.cGens, N3Split.Minus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [gensOK, N3Split.Minus.sGens1, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq,
      idK_eq, ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens, N3Split.Minus.tGens,
      splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Minus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [mulK_sq_bne (j := 11) (by norm_num)]
      simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB_eq_P]
      refine all_range_of_blocks (m := EnN3MS1.m) (s := 9) (nb := 32) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Minus.sReps1, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3M, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · right
        decide +kernel
      · left
        exact candB_false_of_cent sE1_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs1N3M.getD 1 []) (centKs1N3M.getD 1 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · right
        decide +kernel
      · left
        exact candB_false_of_cent sE1_okN3M (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs1N3M.getD 3 []) (centKs1N3M.getD 3 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_sixteen_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        exact candB_false_of_cent sE1_okN3M (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs1N3M.getD 4 []) (centKs1N3M.getD 4 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_sixteen_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
      · left
        exact candB_false_of_cent sE1_okN3M (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl) (centTs1N3M.getD 5 []) (centKs1N3M.getD 5 [])
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel)
          (by decide +kernel)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, List.all_cons, List.all_nil,
            mulVecK_zero, beq_self_eq_true, Bool.true_and, Bool.and_true, mulVecK_one_beq,
            mulVecK_two_beq]; decide +kernel)
          (by decide +kernel) (by simp only [wN3M, decE_keys_size]; decide +kernel)
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3M, memK_decE_eq hM (by decide +kernel)]
    quickRfl

set_option maxHeartbeats 0 in
theorem tau1_okN3M : tauChk1 wN3M = true := by
  have hS : sortedK (decE EnN3MS1.D EnN3MS1.m).keys = true := (Enum.of_enumOK sE1_okN3M).2.1
  have hfc : fixCount N3Split.Minus.tauK = 64 := by
    rw [fixCount_eq_P]
    decide +kernel
  have hB : fixLB N3Split.Minus.tauK [1024, 256, 96, 16, 4, 1] = true := by
    rw [fixLB_eq_P]
    decide +kernel
  obtain ⟨hcc, hko⟩ := commKer_of_orb (s := N3Split.Minus.tauK) sE1_okN3M
    (centTs1N3M.getD 6 []) (centKs1N3M.getD 6 [])
    (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel) (by decide +kernel)
    (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq]; decide +kernel) (by decide +kernel)
    (by simp only [wN3M, decE_keys_size]; decide +kernel)
  simp only [tauChk1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, hfc⟩, ?_⟩, ?_⟩
  · simp only [wN3M, memK_decE_eq hS (by decide +kernel)]
    quickRfl
  · rw [hcc]
    decide +kernel
  · rw [kerCount, hko]
    simp only [fixesOn_fixVecs_basis hB hfc, fixesOn_P (vs := [1024, 256, 96, 16, 4, 1]) (by decide),
      wN3M, decE_getD]
    decide +kernel
  · simp only [invPair, mulK_eq, idK_eq]
    quickRfl

end CertificateChecks.KernelO8
