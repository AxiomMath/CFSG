module

public import Certificates.Kernel.OmegaEight.N3PW
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

@[expose] noncomputable def candPN3 (m : ℕ) : Bool :=
  !(enMemK EnN3PC2.D EnN3PC2.m (mul12K m m) && fpowAuxK 64 m 256 ID12 == ID12 &&
      N3Split.Plus.samples.all fun c =>
        enMemK EnN3PC2.D EnN3PC2.m (mul12K (mul12K m c) (fpowAuxK 64 m 255 ID12))) ||
    N3Split.Plus.reps.any fun r => enMemK EnN3PC.D EnN3PC.m (mul12K r.2 m)

@[expose] noncomputable def candChunkN3 (a b k : ℕ) : Bool :=
  (List.range (2 ^ 12)).all fun c => candPN3 (linComb (N3pLin a b).2.1 (k * 2 ^ 12 + c))

theorem candP_eqN3 :
    (fun m => !(candFilter wN3P.c2E N3Split.Plus.samples m) ||
      repOK wN3P.cE N3Split.Plus.reps m) = candPN3 := by
  have hsC : sortedK (decE EnN3PC.D EnN3PC.m).keys = true := (Enum.of_enumOK cE_okN3P).2.1
  have hs2 : sortedK (decE EnN3PC2.D EnN3PC2.m).keys = true := (Enum.of_enumOK c2E_okN3P).2.1
  funext m
  simp only [candFilter, repOK, wN3P, fpowK_eq, mulK_eq, idK_eq,
    memK_decE_eq hsC (by decide +kernel), memK_decE_eq hs2 (by decide +kernel), candPN3]

set_option maxHeartbeats 0 in
theorem chunksN3_00 : ∀ k < 2 ^ 4, candChunkN3 0 0 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
theorem chunksN3_01 : ∀ k < 2 ^ 4, candChunkN3 0 1 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
theorem chunksN3_10 : ∀ k < 2 ^ 0, candChunkN3 1 0 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
theorem chunksN3_11 : ∀ k < 2 ^ 0, candChunkN3 1 1 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
theorem cand_okN3P : candChk wN3P = true := by
  simp only [candChk, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have ht : (tuples wN3P).length = 2 := by
      simp only [tuples, wN3P, decE_toList, idK_eq]
      decide +kernel
    have hc : N3Split.Plus.cases.length = 2 := rfl
    rw [candCheckW, List.all_eq_true]
    intro a ha
    rw [List.mem_range, hc] at ha
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range, ht] at hb
    rw [Bool.and_eq_true, candP_eqN3]
    constructor
    · simp only [linCheckWith, linRec, conPart_eq, tuples, wN3P, decE_toList, idK_eq,
        N3Split.Plus.cases, mulK_eq]
      interval_cases a <;> interval_cases b <;> decide +kernel
    · have h16 : ∀ b < 2, (wN3P.lin 0 b).2.2.length = 16 := by decide
      have h12 : ∀ b < 2, (wN3P.lin 1 b).2.2.length = 12 := by decide
      interval_cases a <;> interval_cases b
      · exact spanAll_of_chunks (s := 12) (by rw [h16 0 (by norm_num)]; norm_num)
          fun k hk => chunksN3_00 k (by rwa [h16 0 (by norm_num)] at hk)
      · exact spanAll_of_chunks (s := 12) (by rw [h16 1 (by norm_num)]; norm_num)
          fun k hk => chunksN3_01 k (by rwa [h16 1 (by norm_num)] at hk)
      · exact spanAll_of_chunks (s := 12) (by rw [h12 0 (by norm_num)])
          fun k hk => chunksN3_10 k (by rwa [h12 0 (by norm_num)] at hk)
      · exact spanAll_of_chunks (s := 12) (by rw [h12 1 (by norm_num)])
          fun k hk => chunksN3_11 k (by rwa [h12 1 (by norm_num)] at hk)
  · simp only [invPair, mulK_eq, idK_eq]
    decide +kernel
  · have hs2 : sortedK (decE EnN3PC2.D EnN3PC2.m).keys = true := (Enum.of_enumOK c2E_okN3P).2.1
    have h : (N3Split.Plus.samples.all fun c => enMemK EnN3PC2.D EnN3PC2.m c) = true := by
      decide +kernel
    rw [List.all_eq_true] at h ⊢
    intro c hc
    have := h c hc
    rwa [← memK_decE_eq hs2 (by decide +kernel)] at this

end CertificateChecks.KernelO8
