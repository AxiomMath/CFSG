module

public import Certificates.Kernel.OmegaEight.N3PW
public import Certificates.Kernel.OmegaEight.PnSWEq
public import CFSG.Certificates.Kernel.O8N3Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

set_option maxHeartbeats 0 in
theorem s0_okN3P : sChk0 wN3P = true := by
  have hS : sortedK (decE EnN3PS0.D EnN3PS0.m).keys = true := (Enum.of_enumOK sE0_okN3P).2.1
  have hM : sortedK (decE EnN3PM0.D EnN3PM0.m).keys = true := (Enum.of_enumOK mE0_okN3P).2.1
  simp only [sChk0, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE0_okN3P⟩, ?_⟩, ?_⟩, ?_⟩, mE0_okN3P⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Plus.base,
      N3Split.Plus.cGens, N3Split.Plus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [gensOK, N3Split.Plus.sGens0, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
      ← Array.all_toList, N3Split.Plus.base, N3Split.Plus.cGens, N3Split.Plus.tGens, splitCGens,
      splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB, mulVecK_eq]
      refine all_range_of_blocks (m := EnN3PS0.m) (s := 9) (nb := 32) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Plus.sReps0, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3P, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | rfl
      iterate 2
        right
        decide +kernel
      all_goals left
      iterate 2
        exact candB_false_of_zfix (vs := [0, 1, 80]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl)
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq]
              exact all_range_of_blocks (m := EnN3PS0.m) (s := 12) (nb := 4)
                (by decide +kernel) fun b hb => by interval_cases b <;> decide +kernel)
      exact candB_false_of_zfix (vs := [0, 1, 2]) (by decide) (by decide)
        (by simp only [mulVecK_eq]; quickRfl)
        (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq]
            exact all_range_of_blocks (m := EnN3PS0.m) (s := 12) (nb := 4)
              (by decide +kernel) fun b hb => by interval_cases b <;> decide +kernel)
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3P, memK_decE_eq hM (by decide +kernel)]
    quickRfl

set_option maxHeartbeats 0 in
theorem tau0_okN3P : tauChk0 wN3P = true := by
  have hS : sortedK (decE EnN3PS0.D EnN3PS0.m).keys = true := (Enum.of_enumOK sE0_okN3P).2.1
  simp only [tauChk0, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wN3P, memK_decE_eq hS (by decide +kernel)]
    quickRfl
  · rw [commCount_eq, length_filter_range_blocks (s := 12) (nb := 4)
      (C := fun b => [64, 64, 64, 64].getD b 0)
      (by simp only [wN3P, decE_keys_size]; decide +kernel)
      (fun b hb => by
        interval_cases b <;>
          (simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel))]
    decide
  · rw [fixCount_eq]
    decide +kernel
  · rw [kerCount, kerOn_eq, length_filter_range_blocks (s := 12) (nb := 4)
      (C := fun b => [1, 0, 1, 0].getD b 0) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      (fun b hb => by
        interval_cases b <;> (simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, fixesOn,
          fixVecs_eq, mulVecK_eq]; decide +kernel))]
    decide
  · simp only [invPair, mulK_eq, idK_eq]
    quickRfl

set_option maxHeartbeats 0 in
theorem s1_okN3P : sChk1 wN3P = true := by
  have hS : sortedK (decE EnN3PS1.D EnN3PS1.m).keys = true := (Enum.of_enumOK sE1_okN3P).2.1
  have hM : sortedK (decE EnN3PM1.D EnN3PM1.m).keys = true := (Enum.of_enumOK mE1_okN3P).2.1
  simp only [sChk1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, sE1_okN3P⟩, ?_⟩, ?_⟩, ?_⟩, mE1_okN3P⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Plus.base,
      N3Split.Plus.cGens, N3Split.Plus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [gensOK, N3Split.Plus.sGens1, slpGens, runK_eq, fpowK_eq, invPair, mulK_eq, idK_eq,
      ← Array.all_toList, N3Split.Plus.base, N3Split.Plus.cGens, N3Split.Plus.tGens, splitCGens,
      splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Plus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB, mulVecK_eq]
      refine all_range_of_blocks (m := EnN3PS1.m) (s := 9) (nb := 32) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Plus.sReps1, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3P, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      pick_goal 3
      iterate 2
        right
        decide +kernel
      all_goals left
      rotate_left
      iterate 2
        exact candB_false_of_zfix (vs := [0, 1, 80]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl)
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq]
              exact all_range_of_blocks (m := EnN3PS1.m) (s := 12) (nb := 4)
                (by decide +kernel) fun b hb => by interval_cases b <;> decide +kernel)
      all_goals
        exact candB_false_of_zfix (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl)
          (by simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq]
              exact all_range_of_blocks (m := EnN3PS1.m) (s := 12) (nb := 4)
                (by decide +kernel) fun b hb => by interval_cases b <;> decide +kernel)
  · simp only [wN3P, decE_keys_size]
    decide +kernel
  · simp only [wN3P, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3P, memK_decE_eq hM (by decide +kernel)]
    quickRfl

set_option maxHeartbeats 0 in
theorem tau1_okN3P : tauChk1 wN3P = true := by
  have hS : sortedK (decE EnN3PS1.D EnN3PS1.m).keys = true := (Enum.of_enumOK sE1_okN3P).2.1
  simp only [tauChk1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [wN3P, memK_decE_eq hS (by decide +kernel)]
    quickRfl
  · rw [commCount_eq, length_filter_range_blocks (s := 12) (nb := 4)
      (C := fun b => [64, 64, 64, 64].getD b 0)
      (by simp only [wN3P, decE_keys_size]; decide +kernel)
      (fun b hb => by
        interval_cases b <;>
          (simp only [wN3P, decE_getD, decE_keys_size, mulK_eq]; decide +kernel))]
    decide
  · rw [fixCount_eq]
    decide +kernel
  · rw [kerCount, kerOn_eq, length_filter_range_blocks (s := 12) (nb := 4)
      (C := fun b => [1, 0, 1, 0].getD b 0) (by simp only [wN3P, decE_keys_size]; decide +kernel)
      (fun b hb => by
        interval_cases b <;> (simp only [wN3P, decE_getD, decE_keys_size, mulK_eq, fixesOn,
          fixVecs_eq, mulVecK_eq]; decide +kernel))]
    decide
  · simp only [invPair, mulK_eq, idK_eq]
    quickRfl

end CertificateChecks.KernelO8
