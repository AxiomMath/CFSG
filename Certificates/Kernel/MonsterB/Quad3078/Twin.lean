
module

public import Certificates.Kernel.MonsterB.Quad3078.Main
public import Certificates.Kernel.MonsterB.Quad3078.Tree

public section

namespace CertificateChecks.KernelMonB.Quad3078

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.Code CFSG.KC.Q3078 CFSG.KD.Q3078

theorem bitK_eq (n j : ℕ) : bitK n j = if n.testBit j then 1 else 0 := by
  unfold bitK
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change (n >>> j) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  split
  · simp_all
  · simp_all

theorem bitK_le (n j : ℕ) : bitK n j ≤ 1 := by
  rw [bitK_eq]
  split <;> omega

theorem byteK_lt (R i : ℕ) : byteK R i < 256 :=
  Nat.lt_succ_of_le (Nat.and_le_right)

theorem xorK_succ (R base n t : ℕ) :
    xorK R base n (t + 1) = xorK R base n t ^^^ (bitK n t * byteK R (base + t)) := rfl

theorem xorK_lt (R base n t : ℕ) : xorK R base n t < 256 := by
  induction t with
  | zero => exact Nat.zero_lt_succ _
  | succ t ih =>
    rw [xorK_succ]
    have h1 : bitK n t * byteK R (base + t) < 2 ^ 8 := by
      have := bitK_le n t
      have := byteK_lt R (base + t)
      have : bitK n t * byteK R (base + t) ≤ 1 * byteK R (base + t) := Nat.mul_le_mul_right _ ‹_›
      omega
    exact Nat.xor_lt_two_pow (n := 8) ih h1

theorem affK_def (RW CK k n : ℕ) : affK RW CK k n = byteK CK k ^^^ xorK RW (8 * k) n 8 := rfl

theorem affK_lt (RW CK k n : ℕ) : affK RW CK k n < 256 := by
  rw [affK_def]
  exact Nat.xor_lt_two_pow (n := 8) (byteK_lt _ _) (xorK_lt _ _ _ _)

theorem xorK_eq_foldl (R base n : ℕ) (m : ℕ → ℕ) (hm : ∀ j < 8, byteK R (base + j) = m j) :
    ∀ t ≤ 8, xorK R base n t =
      (List.range t).foldl (fun acc j => if n.testBit j then acc ^^^ m j else acc) 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [xorK_succ, ih (by omega), List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, bitK_eq, hm t (by omega)]
    split <;> simp

theorem xorK_eq (R base n : ℕ) (m : ℕ → ℕ) (hm : ∀ j < 8, byteK R (base + j) = m j) :
    xorK R base n 8 = xorRows m n :=
  xorK_eq_foldl R base n m hm 8 le_rfl

theorem affK_eq {k : ℕ} (hk : k < 45) (n : ℕ) : affK RW CK k n = affN k n := by
  rw [affK_def, affN]
  by_cases h : k < 44
  · rw [if_pos h, trans_ok k h, xorK_eq RW (8 * k) n (genRow k) (rows_ok k h)]
  · have e : k = 44 := by omega
    subst e
    rw [if_neg h, trans44, xorK_eq RW (8 * 44) n (fun j => triRows.getD j 0) tri_ok, Nat.zero_xor]

theorem affN_lt {k : ℕ} (hk : k < 45) (n : ℕ) : affN k n < 256 := by
  rw [← affK_eq hk]
  exact affK_lt _ _ _ _

theorem bvec_xor (a b : ℕ) : bvec 8 (a ^^^ b) = bvec 8 a + bvec 8 b := by
  funext i
  simp only [bvec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bvec_zero : bvec 8 0 = 0 := by
  funext i
  simp [bvec]

theorem bvec_foldl (m : ℕ → ℕ) (n : ℕ) : ∀ t,
    bvec 8 ((List.range t).foldl (fun acc j => if n.testBit j then acc ^^^ m j else acc) 0) =
      ∑ j ∈ Finset.range t, (if n.testBit j then (1 : ZMod 2) else 0) • bvec 8 (m j) := by
  intro t
  induction t with
  | zero => simp [bvec_zero]
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      ← ih]
    split
    · simp [bvec_xor, *]
    · simp [*]

theorem bvec_xorRows (m : ℕ → ℕ) (n : ℕ) :
    bvec 8 (xorRows m n) = ∑ j : Fin 8, bvec 8 n j • bvec 8 (m j) := by
  rw [xorRows, bvec_foldl, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem affN_spec' {k : ℕ} (hk : k < 45) (n : ℕ) (hn : n < 256) :
    bvec 8 (affN k n) = affM k (bvec 8 n) ∧ affN k n < 256 := by
  refine ⟨?_, affN_lt hk n⟩
  rw [affN, affM]
  by_cases h : k < 44
  · rw [if_pos h, if_pos h, bvec_xor, bvec_xorRows]
    rfl
  · rw [if_neg h, if_neg h, bvec_xorRows]
    rfl

theorem keepK_def (t : ℕ) :
    keepK RW CK ZM t = Nat.beq (bitK ZM (affK RW CK (t / 256) (t % 256))) (bitK ZM (t % 256)) :=
  rfl

theorem qN_affN' {k : ℕ} (hk : k < 45) {n : ℕ} (hn : n < 256) : qN (affN k n) = qN n := by
  have h := Nat.eq_of_beq_eq_true (keepK_def _ ▸ keep (256 * k + n) (by omega))
  rw [show (256 * k + n) / 256 = k by omega,
    show (256 * k + n) % 256 = n by omega, bitK_eq, bitK_eq, affK_eq hk] at h
  have h1 := zm_ok _ (affN_lt hk n)
  have h2 := zm_ok _ hn
  revert h h1 h2
  cases ZM.testBit (affN k n) <;> cases ZM.testBit n <;> cases qN (affN k n) <;> cases qN n <;>
    simp

theorem affTab_get' {k : ℕ} (hk : k < 45) {n : ℕ} (hn : n < 256) : (affTab[k]!)[n]! = affN k n := by
  simp [affTab, getElem!_pos, hk, hn]

theorem zeroTab_get' {n : ℕ} (hn : n < 256) : zeroTab[n]! = !qN n := by
  simp [zeroTab, getElem!_pos, hn]

theorem affTab_size' : affTab.size = 45 := by
  simp [affTab]

end CertificateChecks.KernelMonB.Quad3078

end
