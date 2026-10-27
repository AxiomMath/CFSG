module

public import Certificates.Kernel.OmegaEight.SB3880

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

@[expose] noncomputable def vAt (c : ℕ) : Bool :=
  decide (vSK c < 512) && (c == 0 || vSK c == Nat.xor (vSK (treeK 0 65535 c)) (2 ^ treeK 16 15 c))

theorem all_range_blocks {P : ℕ → Bool} {B n : ℕ}
    (h : ∀ s < n, (List.range' (B * s) B).all P = true) : (List.range (B * n)).all P = true := by
  rw [List.all_eq_true]
  intro c hc
  have hc' := List.mem_range.1 hc
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hc'
  have hs : c / B < n := (Nat.div_lt_iff_lt_mul hB).2 (by rwa [Nat.mul_comm])
  have e := Nat.div_add_mod c B
  have hm := Nat.mod_lt c hB
  exact List.all_eq_true.1 (h _ hs) c (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem sVecOK_of (h : ∀ s < 8, (List.range' (8192 * s) 8192).all vAt = true) :
    sVecOK vSArr = true := by
  unfold sVecOK
  simp only [vSArr_get, sTree_par, sTree_pj]
  have h0 : vSK 0 = 0 := by decide +kernel
  rw [h0, beq_self_eq_true, Bool.true_and]
  exact all_range_blocks (B := 8192) (n := 8) h

end CertificateChecks.KernelO8.SB3880

end
