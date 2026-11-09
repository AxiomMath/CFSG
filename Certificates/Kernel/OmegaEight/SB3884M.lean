module

public import Certificates.Kernel.OmegaEight.SB3884

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def par5Lit : ℕ := nat_lit 2523490710

@[expose] def par5 (x : ℕ) : Bool := (par5Lit >>> (x &&& 31)) &&& 1 == 1

theorem chiV_land5 {b v : ℕ} : ∀ n, n ≤ 10 → chiV n b v = chiV n 1023 (v &&& b)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [chiV_succ, chiV_succ, chiV_land5 n (by omega), Nat.testBit_land, Nat.testBit_land,
      Nat.testBit_land, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl, Nat.testBit_two_pow_sub_one,
      decide_eq_true (by omega : n < 10), Bool.and_true]

theorem chiV_31 {v : ℕ} : ∀ n, n ≤ 5 → chiV n 31 v = chiV n 1023 v
  | 0, _ => rfl
  | n + 1, hn => by
    rw [chiV_succ, chiV_succ, chiV_31 n (by omega), Nat.testBit_land, Nat.testBit_land,
      show (31 : ℕ) = 2 ^ 5 - 1 from rfl, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl,
      Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
      decide_eq_true (by omega : n < 5), decide_eq_true (by omega : n < 10)]

theorem par5_all : (List.range 32).all (fun x => chiV 5 1023 x == par5 x) = true := by
  decide +kernel

theorem chiV5_eq (b v : ℕ) : chiV 5 b v = par5 (v &&& b) := by
  rw [chiV_land5 5 (by norm_num), ← chiV_31 5 le_rfl, chiV_land5 (b := 31) 5 (by norm_num)]
  have h : (v &&& b) &&& 31 < 32 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  rw [beq_iff_eq.1 (List.all_eq_true.1 par5_all _ (List.mem_range.2 h))]
  unfold par5
  rw [Nat.and_assoc (v &&& b) 31 31, Nat.and_self 31]

@[expose] def cntMaskF (b : ℕ) (q : ℕ → Bool) (L : List (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  (L.filter fun e => !par5 (e.2.2.2 &&& b) && q e.1).length

@[expose] def thMaskF (smul : ℕ → ℕ → ℕ) (e : ℕ) (gs : List ℕ) (ps : List (ℕ × ℕ)) (b : ℕ) :
    Bool :=
  b == 0 || par5 (vecOf (dblL smul gs ps) (l2T.getD e 0) &&& b) ||
    (l2PLit.getD e []).contains
      (cntMaskF b (fun c => smul c c == 0 && c != 0) (dblL smul gs ps),
        cntMaskF b (fun c => smul c c != 0 && smul (smul c c) (smul c c) == 0) (dblL smul gs ps))

theorem thMask_eq : thMask = thMaskF := by
  funext smul e gs ps b
  simp only [thMask, thMaskF, cntMask, cntMaskF, chiV5_eq]

end CertificateChecks.KernelO8.SB3884

end
