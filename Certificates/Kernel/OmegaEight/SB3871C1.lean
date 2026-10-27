module

public import Certificates.Kernel.OmegaEight.SB3871

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem all_range_chunks {P : ℕ → Bool} (n k : ℕ)
    (h : ∀ s < k, (List.range' (n * s) n).all P = true) : (List.range (n * k)).all P = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_range] at hx
  have hn : 0 < n := Nat.pos_of_ne_zero fun e => by simp [e] at hx
  have hs : x / n < k := Nat.div_lt_of_lt_mul hx
  exact List.all_eq_true.1 (h _ hs) x (List.mem_range'_1.2 ⟨Nat.mul_div_le x n |>.trans_eq' (by ring),
    by have := Nat.lt_mul_div_succ x hn; linarith⟩)

theorem a9K_lin (v : ℕ) : a9K.lin v = linK v := a9LinTab_get v

theorem a9K_co (c : ℕ) : a9K.co c = coK c := a9CoTab_get c

set_option maxHeartbeats 0 in
theorem check1 : sAutCheck1 = true := by
  unfold sAutCheck1
  simp only [sMul_eqK, sInv_eqK, a9K_lin, a9K_co, sAutData, sNfTab_get, sTree_par, sTree_pj, sTree_dep,
    sConj, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold invOK
    refine all_range_chunks 16384 4 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · decide +kernel
  · refine all_range_chunks 64 8 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · refine all_range_chunks 8192 8 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · decide +kernel
  · refine all_range_chunks 8192 8 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold treeOK
    refine all_range_chunks 16384 4 fun s hs => ?_
    interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
