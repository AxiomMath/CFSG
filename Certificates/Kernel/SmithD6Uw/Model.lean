module

public import Certificates.Kernel.SmithD6Wt.Math
public import Certificates.Kernel.SmithD6Trees.Facts
public import CFSG.Certificates.Kernel.SmithD6Search
public import CFSG.Certificates.Kernel.SmithD6IdSound

public section

namespace CertificateChecks.SmithD6Uw

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KC.SmithD6Search
  CFSG.GF2Type.SmithTypeE.DMod CertificateChecks.SmithD6Wt

theorem lineOf_eq {u w : ℕ} (h1 : u < w) (h2 : w < u ^^^ w) : lineOf u w = lineIdx u w := by
  unfold lineOf lineIdx3
  have e1 : min u (min w (u ^^^ w)) = u := by omega
  have e2 : max u (max w (u ^^^ w)) = u ^^^ w := by omega
  dsimp only
  rw [e1, e2, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem exC_inj {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : exC a = exC b) : a = b := by
  apply eq_of_decode32_eq ha hb
  apply exL_injective
  rw [← decode64_exC, ← decode64_exC, h]

theorem decode64_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : decode64 a = decode64 b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro T
  by_cases hT : T < 64
  · have := congrFun h ⟨T, hT⟩
    simp only [decode64_apply] at this
    exact bit_injective this
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem exC_xor (a b : ℕ) : exC (a ^^^ b) = exC a ^^^ exC b := by
  apply decode64_inj (exC_lt_two_pow _) (Nat.xor_lt_two_pow (exC_lt_two_pow _) (exC_lt_two_pow _))
  rw [decode64_xor, decode64_exC, decode64_exC, decode64_exC, decode32_xor, map_add]

theorem exC_one : exC 1 = 1 := by decide +kernel

theorem testBit_exC_63 (s : ℕ) : (exC s).testBit 63 = s.testBit 31 := by
  have he : ∀ c : Fin 32, (evF c).val = 63 ↔ c = 31 := by decide +kernel
  rw [testBit_exC]
  by_cases hs : s.testBit 31 = true
  · rw [hs]
    exact decide_eq_true ⟨31, (he 31).2 rfl, hs⟩
  · rw [Bool.eq_false_iff.2 hs]
    refine decide_eq_false fun ⟨c, hc, hc'⟩ => hs ?_
    rw [(he c).1 hc] at hc'
    exact hc'

theorem applyCols_of_liftT {k x y : ℕ} {p : ℕ × ℕ} {ts : List (ℕ × ℕ × Bool)}
    (hl : linePair k = p) (hts : rhoTOK p.1 p.2 ts = true) (hy : y < 2 ^ 32)
    (h : liftT ts (exC x) = exC y) : applyCols (tvCols k) x = y := by
  apply eq_of_decode32_eq (applyCols_tvCols_lt k x) hy
  apply exL_injective
  rw [decode32_applyCols (tvCols_size k), exL_colsLin_tvCols, hl, ← decode64_exC, ← decode64_exC,
    ← h, decode64_liftT hts (exC_lt_two_pow x)]

theorem memB_iff_mem {t : KT} {K : List ℕ} (hf : ∀ i (hi : i < K.length), t.find K[i] = i + 1)
    (hs : ∀ x v, t.find x = v + 1 → ∃ hv : v < K.length, K[v] = x) (x : ℕ) :
    t.memB x = true ↔ x ∈ K := by
  unfold KT.memB
  constructor
  · intro h
    have hp : 0 < t.find x := Nat.le_of_ble_eq_true h
    obtain ⟨hv, hx⟩ := hs x (t.find x - 1) (by omega)
    rw [← hx]
    exact List.getElem_mem hv
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    rw [hf i hi]
    exact Nat.ble_eq_true_of_le (Nat.succ_pos i)

theorem getElem_eq_map {L64 L : List ℕ} (h : L64 = L.map exC) {j : ℕ} (hj : j < L64.length) :
    L64[j] = exC (L[j]'(by rw [h, List.length_map] at hj; exact hj)) := by
  subst h
  rw [List.getElem_map]

theorem wt64_get {j : ℕ} (hj : j < J.wt64C.flatten.length) :
    J.wt64C.flatten[j] = exC (J.wtC.flatten[j]'(by
      rw [wt64_eq_map.1, List.length_map] at hj; exact hj)) :=
  getElem_eq_map wt64_eq_map.1 hj

theorem wtC_lt_mem {x : ℕ} (hx : x ∈ J.wtC.flatten) : x < 2 ^ 32 :=
  lt_of_lt_of_eq (wt64_eq_map.2 x hx) (by norm_num)

theorem wtC_lt {j : ℕ} (hj : j < J.wtC.flatten.length) : J.wtC.flatten[j] < 2 ^ 32 :=
  wtC_lt_mem (List.getElem_mem hj)

theorem wt0 : ∃ h : 0 < J.wtC.flatten.length, J.wtC.flatten[0] = 1 := by
  have hl : 0 < J.wtC.flatten.length := by rw [wtC_flatten_length]; norm_num
  refine ⟨hl, ?_⟩
  have h := first.1
  rwa [getD_eq hl] at h

section Model

variable (hW : wtArr.toList = J.wtC.flatten)
include hW

theorem wtIdx_eq (x : ℕ) : wtIdx x = KT.idx 75735 x wtTree := by
  obtain ⟨hp, hn, hf, hs⟩ := SmithD6Trees.wt_facts
  unfold wtIdx
  exact search_eq_idx hW hn (by norm_num) hp hf hs x

theorem wtIdx_get {v : ℕ} (hv : v < J.wtC.flatten.length) : wtIdx J.wtC.flatten[v] = v := by
  obtain ⟨-, -, hf, hs⟩ := SmithD6Trees.wt_facts
  rw [wtIdx_eq hW]
  exact (KT.idx_eq (N := 75735) hf hs _).1 v hv rfl

theorem wtIdx_lt_iff (x : ℕ) : wtIdx x < 75735 ↔ x ∈ J.wtC.flatten := by
  obtain ⟨-, -, hf, hs⟩ := SmithD6Trees.wt_facts
  constructor
  · intro h
    by_contra hx
    rw [wtIdx_eq hW, (KT.idx_eq (N := 75735) hf hs x).2
      (fun i hi hix => hx (hix ▸ List.getElem_mem hi))] at h
    exact absurd h (lt_irrefl _)
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [wtIdx_get hW hi]
    rw [wtC_flatten_length] at hi
    exact hi

theorem wt_eq {j : ℕ} (hj : j < J.wtC.flatten.length) : wt j = J.wtC.flatten[j] := by
  have : wtArr[j]! = J.wtC.flatten[j]! := by rw [← hW, Array.getElem!_toList]
  rw [wt, this, getElem!_pos _ j hj]

end Model

end CertificateChecks.SmithD6Uw

end
