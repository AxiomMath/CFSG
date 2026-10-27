module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
public import Certificates.Kernel.OmegaEight.SB3880VD

public section

namespace CertificateChecks.KernelO8.SB3880

open CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def parLit : ℕ := nat_lit 74146578472109212997136511361482254487891641386702620145716156204378150869765806841403385319857558565549512234915555076261584853249966913297281241601813858394614116897041089993247811088911534355298428851353473257124296480147861272197456166579083811387730393363010282273585299534106637649680409542459252107670

@[expose] def parK (x : ℕ) : Bool := Nat.land (Nat.shiftRight parLit x) 1 == 1

theorem chiV_land {b v : ℕ} : ∀ n, n ≤ 10 → chiV n b v = chiV n 1023 (v &&& b)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [chiV_succ, chiV_succ, chiV_land n (by omega), Nat.testBit_land, Nat.testBit_land,
      Nat.testBit_land, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl, Nat.testBit_two_pow_sub_one,
      decide_eq_true (by omega : n < 10), Bool.and_true]

theorem parK_all : (List.range 1024).all (fun x => chiV 10 1023 x == parK x) = true := by
  decide +kernel

theorem chiV_fast {b : ℕ} (hb : b < 1024) (v : ℕ) : chiV 10 b v = parK (v &&& b) := by
  rw [chiV_land 10 le_rfl]
  have h : v &&& b < 1024 := lt_of_le_of_lt Nat.and_le_right hb
  exact beq_iff_eq.1 (List.all_eq_true.1 parK_all _ (List.mem_range.2 h))

@[expose] def o4Lit : List ℕ :=
  [3200, 3456, 3904, 3904, 2368, 2368, 2368, 2368, 2976, 2976, 2976, 2976, 2368, 2368, 2368, 2368]

@[expose] def o4c (mulf : ℕ → ℕ → ℕ) (vecf : ℕ → ℕ) (b : ℕ) (L : List ℕ) : ℕ :=
  (L.filter fun c => !parK (vecf c &&& b) &&
    (mulf c c != 0 && mulf (mulf c c) (mulf c c) == 0)).length

@[expose] def maskK (mulf : ℕ → ℕ → ℕ) (vecf : ℕ → ℕ) (RW : List (ℕ × ℕ)) (IV : List ℕ)
    (b : ℕ) : Bool :=
  b == 512 || b == 768 ||
    (RW.any fun p => parK ((vecf (mulf p.1 (t1Gens.getD p.2 0)) ^^^ vecf p.1 ^^^ 2 ^ p.2) &&& b)) ||
    (IV.filter fun v => !parK (v &&& b)).length != 3839 ||
    o4c mulf vecf b (List.range 131072) != 41216

theorem filter_length_blocks (p : ℕ → Bool) (B : ℕ) :
    ∀ n, ((List.range (B * n)).filter p).length =
      ((List.range n).map fun s => ((List.range' (B * s) B).filter p).length).sum
  | 0 => by simp
  | n + 1 => by
    rw [Nat.mul_succ, List.range_add, List.filter_append, List.length_append,
      filter_length_blocks p B n, List.range_succ, List.map_append, List.sum_append,
      ← List.range'_eq_map_range]
    simp

theorem o4c_blocks (mulf : ℕ → ℕ → ℕ) (vecf : ℕ → ℕ) (b : ℕ) :
    o4c mulf vecf b (List.range 131072) =
      ((List.range 16).map fun s => o4c mulf vecf b (List.range' (8192 * s) 8192)).sum := by
  unfold o4c
  exact filter_length_blocks _ 8192 16

theorem l2eCharOK_of {j : ℕ} {mulf : ℕ → ℕ → ℕ} {vec : Array ℕ} {vecf : ℕ → ℕ}
    {RW : List (ℕ × ℕ)} {IV : List ℕ} (hmul : t1Mul (s2F j) (s2Z j) = mulf)
    (hvec : ∀ c, vec[c]! = vecf c)
    (h1 : (RW.all fun p => decide (p.1 < 131072) && decide (p.2 < 10)) = true)
    (h2 : IV = (kInv mulf 131072).map vecf)
    (hm : (List.range 1024).all (maskK mulf vecf RW IV) = true) :
    l2eCharOK j vec RW IV = true := by
  unfold l2eCharOK
  dsimp only
  rw [hmul, h1, Bool.true_and, ← List.map_congr_left (fun c _ => (hvec c).symm), ← h2,
    beq_self_eq_true, Bool.true_and]
  simp only [hvec, s2Rel]
  rw [List.all_eq_true] at hm ⊢
  intro b hb
  have hb' := List.mem_range.1 hb
  have h := hm b hb
  unfold maskK o4c at h
  simp only [chiV_fast hb']
  exact h

end CertificateChecks.KernelO8.SB3880

end
