module

public import Certificates.Kernel.OmegaEight.N3MW
public import CFSG.Certificates.Kernel.O8N3Sound
public import Certificates.Kernel.OmegaEight.PnSWEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.O8MinusSound
public import CFSG.Certificates.Kernel.O8NodeSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

set_option maxHeartbeats 0 in
theorem s2_okN3M : s2Chk wN3M = true := by
  have hS : sortedK (decE EnN3MS2.D EnN3MS2.m).keys = true := (Enum.of_enumOK s2E_okN3M).2.1
  have hM : sortedK (decE EnN3MM2.D EnN3MM2.m).keys = true := (Enum.of_enumOK m2E_okN3M).2.1
  simp only [s2Chk, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, s2E_okN3M⟩, ?_⟩, ?_⟩, ?_⟩, m2E_okN3M⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [gensOK, N3Split.Minus.s2Gens, N3Split.Minus.sGens0, slpGens, runK_eq, fpowK_eq,
      invPair, mulK_eq, idK_eq, ← Array.all_toList, N3Split.Minus.base, N3Split.Minus.cGens,
      N3Split.Minus.tGens, splitCGens, splitTGens, kronK_eq]
    quickRfl
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList,
      N3Split.Minus.tGens, splitTGens, kronK_eq]
    quickRfl
  · rw [classCertW, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, idK_eq, fixLB, mulVecK_eq]
      refine all_range_of_blocks (m := EnN3MS2.m) (s := 9) (nb := 64) (by decide +kernel)
        fun b hb => ?_
      interval_cases b <;> decide +kernel
    · rw [List.all_eq_true]
      intro r hr
      simp only [N3Split.Minus.s2Reps, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨?_, ?_⟩
      · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [wN3M, memK_decE_eq hS (by decide +kernel)]; quickRfl)
      rcases hr with rfl | rfl | rfl | rfl | hr
      · right
        decide +kernel
      on_goal 4 => rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      all_goals left
      pick_goal 3
      iterate 2
        exact candB_false_of_zfix (vs := [0, 1, 16]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq]
              exact all_range_of_blocks (m := EnN3MS2.m) (s := 12) (nb := 8)
                (by decide +kernel) fun b hb => by interval_cases b <;> decide +kernel)
      all_goals
        exact candB_false_of_zfix (vs := [0, 1, 2]) (by decide) (by decide)
          (by simp only [mulVecK_eq]; quickRfl)
          (by simp only [wN3M, decE_getD, decE_keys_size, mulK_eq, mulVecK_eq]
              exact all_range_of_blocks (m := EnN3MS2.m) (s := 12) (nb := 8)
                (by decide +kernel) fun b hb => by interval_cases b <;> decide +kernel)
  · simp only [wN3M, decE_keys_size]
    decide +kernel
  · simp only [wN3M, gensIn, memK_decE_eq hS (by decide +kernel), ← Array.all_toList]
    quickRfl
  · simp only [wN3M, memK_decE_eq hM (by decide +kernel)]
    quickRfl

end CertificateChecks.KernelO8
