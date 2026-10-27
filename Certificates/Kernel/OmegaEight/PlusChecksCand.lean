module

public import Certificates.Kernel.OmegaEight.PlusW
public import CFSG.Certificates.Kernel.O8PlusSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

@[expose] noncomputable def candP (m : ℕ) : Bool :=
  !(enMemK EnC2.D EnC2.m (mul12K m m) && fpowAuxK 64 m 256 ID12 == ID12 &&
      Plus.samples.all fun c =>
        enMemK EnC2.D EnC2.m (mul12K (mul12K m c) (fpowAuxK 64 m 255 ID12))) ||
    Plus.reps.any fun r => enMemK EnCP.D EnCP.m (mul12K r.2 m)

@[expose] noncomputable def candChunk (a b k : ℕ) : Bool :=
  (List.range (2 ^ 12)).all fun c => candP (linComb (PwLin a b).2.1 (k * 2 ^ 12 + c))

theorem candP_eq : (fun m => !(candFilter wP.c2E Plus.samples m) || repOK wP.cE Plus.reps m) =
    candP := by
  have hsC : sortedK (decE EnCP.D EnCP.m).keys = true := (Enum.of_enumOK cE_ok).2.1
  have hs2 : sortedK (decE EnC2.D EnC2.m).keys = true := (Enum.of_enumOK c2E_ok).2.1
  funext m
  simp only [candFilter, repOK, wP, fpowK_eq, mulK_eq, idK_eq,
    memK_decE_eq hsC (by decide +kernel), memK_decE_eq hs2 (by decide +kernel), candP]

set_option maxHeartbeats 0 in
theorem chunks00 : ∀ k < 2 ^ 4, candChunk 0 0 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
theorem chunks01 : ∀ k < 2 ^ 4, candChunk 0 1 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem chunks10 : ∀ k < 2 ^ 0, candChunk 1 0 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem chunks11 : ∀ k < 2 ^ 0, candChunk 1 1 k = true := by
  intro k hk
  interval_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
theorem cand_okP : candChk wP = true := by
  simp only [candChk, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have ht : (tuples wP).length = 2 := by
      simp only [tuples, wP, decE_toList, idK_eq]
      decide +kernel
    have hc : Plus.cases.length = 2 := rfl
    rw [candCheckW, List.all_eq_true]
    intro a ha
    rw [List.mem_range, hc] at ha
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range, ht] at hb
    rw [Bool.and_eq_true, candP_eq]
    constructor
    · simp only [linCheckWith, linRec, conPart_eq, tuples, wP, decE_toList, idK_eq, Plus.cases,
        mulK_eq]
      interval_cases a <;> interval_cases b <;> decide +kernel
    · have h16 : ∀ b < 2, (wP.lin 0 b).2.2.length = 16 := by decide
      have h12 : ∀ b < 2, (wP.lin 1 b).2.2.length = 12 := by decide
      interval_cases a <;> interval_cases b
      · exact spanAll_of_chunks (s := 12) (by rw [h16 0 (by norm_num)]; norm_num)
          fun k hk => chunks00 k (by rwa [h16 0 (by norm_num)] at hk)
      · exact spanAll_of_chunks (s := 12) (by rw [h16 1 (by norm_num)]; norm_num)
          fun k hk => chunks01 k (by rwa [h16 1 (by norm_num)] at hk)
      · exact spanAll_of_chunks (s := 12) (by rw [h12 0 (by norm_num)])
          fun k hk => chunks10 k (by rwa [h12 0 (by norm_num)] at hk)
      · exact spanAll_of_chunks (s := 12) (by rw [h12 1 (by norm_num)])
          fun k hk => chunks11 k (by rwa [h12 1 (by norm_num)] at hk)
  · simp only [invPair, mulK_eq, idK_eq]
    decide +kernel
  · have hs2 : sortedK (decE EnC2.D EnC2.m).keys = true := (Enum.of_enumOK c2E_ok).2.1
    simp only [wP, memK_decE_eq hs2 (by decide +kernel)]
    decide +kernel

end CertificateChecks.KernelO8
