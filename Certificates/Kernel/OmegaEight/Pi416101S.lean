module

public import Certificates.Kernel.OmegaEight.Pi416101K
public meta import Certificates.Kernel.OmegaEight.Pi416101Seal
import Mathlib.Data.List.Dedup

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8

@[expose] noncomputable def piSqEnc : Nat := piSq.foldr (fun x acc => x + 2 ^ 3240 * acc) 0

#kc_seal_list CertificateChecks.KernelO8.piSqL piSqEnc 3600 3240

set_option maxRecDepth 400000 in
theorem piSq_eq : piSq = piSqL := by decide +kernel

@[expose] noncomputable def q8ChunkL (P ks : List Nat) : Bool :=
  ks.all fun k =>
    let B := P.filter fun X => kNat X == k
    B.all fun x => B.all fun y => pairBK piTests x y

theorem q8Chunk_eqL (ks : List Nat) : q8Chunk ks = q8ChunkL piSq ks := rfl

theorem q8Part_eqS (i : ℕ) :
    q8Part i = q8ChunkL piSqL (((piSqL.map kNat).filter fun k => k % 8 == i).dedup) := by
  rw [q8Part_eq, q8Chunk_eqL, piSq_eq]

theorem q8_split (i m : ℕ) (hm : 0 < m)
    (h : ∀ j < m, q8ChunkL piSqL
      (((piSqL.map kNat).filter fun k => k % 8 == i && k % m == j).dedup) = true) :
    q8Part i = true := by
  rw [q8Part_eqS]
  simp only [q8ChunkL] at h ⊢
  rw [List.all_eq_true]
  intro k hk
  have hj := h (k % m) (Nat.mod_lt _ hm)
  rw [List.all_eq_true] at hj
  have hk1 := List.mem_filter.1 (List.mem_dedup.1 hk)
  exact hj k (List.mem_dedup.2 (List.mem_filter.2 ⟨hk1.1, by simpa using hk1.2⟩))

@[expose] noncomputable def q8ChunkLx (P ks : List Nat) (r t : Nat) : Bool :=
  ks.all fun k =>
    let B := P.filter fun X => kNat X == k
    (B.filter fun x => x % r == t).all fun x => B.all fun y => pairBK piTests x y

theorem q8ChunkL_of_x (P ks : List Nat) (r : Nat) (hr : 0 < r)
    (h : ∀ t < r, q8ChunkLx P ks r t = true) : q8ChunkL P ks = true := by
  simp only [q8ChunkL, q8ChunkLx] at h ⊢
  rw [List.all_eq_true]
  intro k hk
  rw [List.all_eq_true]
  intro x hx
  have h1 := h (x % r) (Nat.mod_lt _ hr)
  rw [List.all_eq_true] at h1
  have h2 := h1 k hk
  rw [List.all_eq_true] at h2
  exact h2 x (List.mem_filter.2 ⟨hx, by simp⟩)

end CertificateChecks.KernelO8

end
