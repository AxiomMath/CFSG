module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmegaDefs

namespace CertificateChecks.KernelM24QdQ

open CFSG.EvenSporadicStandard.M24Std CFSG.QuasithinUnique.Setup.X1

theorem foldl_ite_mul (p : ℕ → Bool) (f : ℕ → S24) (l : List ℕ) (a : S24) :
    l.foldl (fun acc k => if p k then acc * f k else acc) a =
      a * (l.map fun k => if p k then f k else 1).prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    split_ifs <;> simp [mul_assoc]

theorem m24Elt_xor (B : List S24)
    (hc : ∀ i < 6, ∀ j < 6, B.getD i 1 * B.getD j 1 = B.getD j 1 * B.getD i 1)
    (hs : ∀ i < 6, B.getD i 1 * B.getD i 1 = 1) (m n : ℕ) :
    m24Elt B (m ^^^ n) = m24Elt B m * m24Elt B n := by
  let K : Subgroup S24 := Subgroup.closure ((fun i => B.getD i 1) '' {i | i < 6})
  have : IsMulCommutative K := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ _
    exact hc i hi j hj)
  have hprod : ∀ f g : ℕ → K, ((List.range 6).map f).prod * ((List.range 6).map g).prod =
      ((List.range 6).map fun k => f k * g k).prod := fun f g => by
    let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := mul_comm' }
    exact List.prod_map_mul.symm
  let w : ℕ → K := fun i =>
    if h : i < 6 then ⟨B.getD i 1, Subgroup.subset_closure ⟨i, h, rfl⟩⟩ else 1
  have hww : ∀ i, w i * w i = 1 := fun i => by
    by_cases h : i < 6
    · exact Subtype.ext (by simpa [w, h] using hs i h)
    · simp [w, h]
  have key : ∀ n, m24Elt B n =
      (((List.range 6).map fun k => if n.testBit k then w k else 1).prod : K) := by
    intro n
    rw [m24Elt, foldl_ite_mul, one_mul, ← K.coe_subtype, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
    have hk6 : k < 6 := List.mem_range.1 hk
    by_cases hb : n.testBit k <;> simp [hb, w, hk6]
  rw [key, key, key, ← Subgroup.coe_mul, hprod]
  refine congrArg (fun x : K => (x : S24)) (congrArg List.prod (List.map_congr_left fun k _ => ?_))
  rw [Nat.testBit_xor]
  cases m.testBit k <;> cases n.testBit k <;> simp [hww]

theorem foldl_xor_map (φ : ℕ → S24) (hφ : ∀ a b, φ (a ^^^ b) = φ a * φ b) (p : ℕ → Bool)
    (c : ℕ → ℕ) (l : List ℕ) (a : ℕ) :
    φ (l.foldl (fun acc i => if p i then acc ^^^ c i else acc) a) =
      l.foldl (fun acc i => if p i then acc * φ (c i) else acc) (φ a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split_ifs <;> simp only [hφ]

def qdCols : List ℕ := [26, 47, 29, 38, 23, 41]

def qdLinC (k : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc i => if k.testBit i then acc ^^^ qdCols.getD i 0 else acc) 0

set_option maxHeartbeats 0 in
theorem e1B_comm : ∀ i ∈ List.range 6, ∀ j ∈ List.range 6,
    m24E1B.getD i 1 * m24E1B.getD j 1 = m24E1B.getD j 1 * m24E1B.getD i 1 ∧
    m24E1B.getD i 1 * m24E1B.getD i 1 = 1 := by
  decide +kernel

theorem qdLinC_lt : ∀ k ∈ List.range 64, qdLinC k < 64 := by decide +kernel

theorem qdLinC_surj : ∀ m ∈ List.range 64, ∃ k ∈ List.range 64, qdLinC k = m := by
  decide +kernel

theorem qdFxTab_24 : ∀ k ∈ List.range 64, qdFxTab.getD k 99 = 24 → k = 0 := by decide +kernel

set_option maxHeartbeats 0 in
theorem qdFix_e1 : ∀ k ∈ List.range 64,
    qdFix (m24Elt m24E1B (qdLinC k)) = qdFxTab.getD k 99 := by
  decide +kernel

theorem qdFix_one : qdFix 1 = 24 := by decide +kernel

theorem e1_xor (m n : ℕ) : m24Elt m24E1B (m ^^^ n) = m24Elt m24E1B m * m24Elt m24E1B n :=
  m24Elt_xor m24E1B (fun i hi j hj => (e1B_comm i (List.mem_range.2 hi) j (List.mem_range.2 hj)).1)
    (fun i hi => (e1B_comm i (List.mem_range.2 hi) i (List.mem_range.2 hi)).2) m n

theorem e1_zero : m24Elt m24E1B 0 = 1 := by simp [m24Elt]

theorem qdQB_getD (i : ℕ) : qdQB.getD i 1 = m24Elt m24E1B (qdCols.getD i 0) := by
  by_cases hi : i < 6
  · have h : ∀ k < 64, m24E1l.getD k 1 = m24Elt m24E1B k := fun k hk => by
      simp [m24E1l, m24Lst, List.getD_eq_getElem?_getD, hk]
    interval_cases i <;> simp only [qdQB, qdCols, List.map_cons, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact h _ (by norm_num)
  · rw [List.getD_eq_default _ _ (by simp [qdQB]; omega),
      List.getD_eq_default _ _ (by simp [qdCols]; omega), e1_zero]

theorem qdQ_eq (k : ℕ) : qdQ k = m24Elt m24E1B (qdLinC k) := by
  rw [qdLinC, foldl_xor_map _ e1_xor, e1_zero, qdQ, m24Elt]
  simp only [qdQB_getD]

theorem qdQ_xor (k j : ℕ) : qdQ (k ^^^ j) = qdQ k * qdQ j := by
  have hc : ∀ i < 6, ∀ j < 6, qdQB.getD i 1 * qdQB.getD j 1 = qdQB.getD j 1 * qdQB.getD i 1 :=
    fun i _ j _ => by rw [qdQB_getD, qdQB_getD, ← e1_xor, ← e1_xor, Nat.xor_comm]
  have hs : ∀ i < 6, qdQB.getD i 1 * qdQB.getD i 1 = 1 := fun i _ => by
    rw [qdQB_getD, ← e1_xor, Nat.xor_self, e1_zero]
  exact m24Elt_xor qdQB hc hs k j

public section

set_option maxHeartbeats 0 in
theorem qdQData : QdQData := by
  have hmem : ∀ m < 64, m24Elt m24E1B m ∈ m24E1l := fun m hm =>
    List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩
  refine ⟨fun s hs => ?_, fun k hk => ?_, fun k _ j _ => (qdQ_xor k j).symm,
    fun k hk j hj h => ?_, fun k hk => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hs
    obtain ⟨k, hk, hkm⟩ := qdLinC_surj m hm
    exact ⟨k, hk, by rw [qdQ_eq, hkm]⟩
  · rw [qdQ_eq]
    exact hmem _ (qdLinC_lt k hk)
  · have h1 : qdQ (k ^^^ j) = 1 := by
      rw [qdQ_xor, h, ← qdQ_xor, Nat.xor_self, qdQ_eq]
      exact e1_zero
    have hkj : k ^^^ j < 64 :=
      Nat.xor_lt_two_pow (n := 6) (List.mem_range.1 hk) (List.mem_range.1 hj)
    have h2 := qdFix_e1 (k ^^^ j) (List.mem_range.2 hkj)
    rw [← qdQ_eq, h1, qdFix_one] at h2
    have h3 := congrArg (· ^^^ j) (qdFxTab_24 _ (List.mem_range.2 hkj) h2.symm)
    simpa [Nat.xor_assoc] using h3
  · rw [qdQ_eq]
    exact qdFix_e1 k hk

end

end CertificateChecks.KernelM24QdQ
