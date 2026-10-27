module

public import Certificates.Kernel.Sporadic.M22Pair5
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Certificates.Kernel.Spor.PK.CertMem

public section

namespace CertificateChecks.KernelSpor.M22Pair5

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

set_option maxRecDepth 100000

attribute [local irreducible] lv cntS cl m22Certificate

private theorem enum_eq : enumeration m22Certificate = products lv := by
  rw [enumeration, lv]

private def ws : List (List ℕ × ℕ) := [([0, 1], 11), ([0, 1, 2, 3], 6), ([0, 1, 1], 5)]

private theorem wordsRel_iff (x y : Equiv.Perm (Fin 22)) :
    WordsRel ws x y ↔
      orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6 ∧ orderOf (x * y * y) = 5 := by
  simp [ws, WordsRel, evalW, letterW, mul_assoc]

private theorem pair_iff {x y : Table} {xg yg : Equiv.Perm (Fin 22)} (hx : Rep 22 x xg)
    (hy : Rep 22 y yg) (hxo : orderOf xg = 2) (hyo : orderOf yg = 4) :
    (pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) = true ↔ WordsRel ws xg yg := by
  rw [Bool.and_eq_true, pairTest_iff perm_faithful hx hy (by norm_num) (by norm_num) hxo hyo
    (by norm_num) (by norm_num),
    ordW_iff perm_faithful (.cons hx (.cons hy (.cons hy .nil))) (by norm_num)]
  simp only [wordsRel_iff, List.prod_cons, List.prod_nil, mul_one, mul_assoc, and_assoc]

private theorem partner_iff (x y : Equiv.Perm (Fin 22)) :
    (decide (WordsRel ws x y) && decide (orderOf y = 4)) = decide (PartnerW x y) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    decide_eq_true_iff, wordsRel_iff, PartnerW]
  tauto

private theorem ordW_gens {a b : Equiv.Perm (Fin 22)} (h : orderOf (a * b * b) = 5) :
    ordW 22 [toTable a, toTable b, toTable b] 5 = true := by
  rw [ordW_iff perm_faithful (.cons (rep_toTable (by norm_num) a)
    (.cons (rep_toTable (by norm_num) b) (.cons (rep_toTable (by norm_num) b) .nil)))
    (by norm_num)]
  simpa [mul_assoc] using h

private theorem decode {L : List (Equiv.Perm (Fin 22))} {a : Equiv.Perm (Fin 22)}
    (ha : orderOf a = 2) (hlen : L.length = 443520)
    (h : (L.map fun h =>
      cntW 22 5 (mask 5) (pkw 5 (1 : Equiv.Perm (Fin 22))) (pkw 5 a) (pkw 5 h)).sum =
        1155 + 1048576 * 768) :
    L.countP (fun h => decide (orderOf h = 2)) = 1155 ∧
      L.countP (fun h => decide (PartnerW a h)) = 768 := by
  rw [List.map_congr_left fun h _ => cntW_pkw (by norm_num) (by norm_num) ha h] at h
  simp only [List.sum_map_add, List.sum_map_mul_left, sum_ite_eq_countP] at h
  have h1 := List.countP_le_length (p := fun h => decide (orderOf h = 2)) (l := L)
  have h2 := List.countP_le_length (p := fun h => decide (PartnerW a h)) (l := L)
  rw [hlen] at h1 h2
  omega

private theorem sum_cntW :
    ((enumeration m22Certificate).map fun h =>
      cntW 22 5 (mask 5) (pkw 5 (1 : Equiv.Perm (Fin 22))) (pkw 5 m22gA) (pkw 5 h)).sum =
      1155 + 1048576 * 768 := by
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have h32 : (22 : Nat) < 2 ^ 32 := by norm_num
  obtain ⟨T0, rest, hlv⟩ : ∃ T0 rest, lv = T0 :: rest := by
    cases h : lv with
    | nil =>
      have := Nat.eq_of_beq_eq_true lens
      rw [h] at this
      simp at this
    | cons T0 rest => exact ⟨T0, rest, rfl⟩
  have hT0 : T0.length ≤ 1 * 22 := by
    have := Nat.le_of_ble_eq_true len₀
    rw [hlv] at this
    simpa using this
  have hcnt : ∀ j, ((products (((T0.drop (1 * j)).take 1) :: rest)).map fun h =>
      cntW 22 5 (mask 5) (pkw 5 (1 : Equiv.Perm (Fin 22))) (pkw 5 m22gA) (pkw 5 h)).sum =
        cntS j := by
    intro j
    have hs : slice j = ((T0.drop (1 * j)).take 1) :: rest := by rw [slice, hlv]; rfl
    rewrite [cntS, I, hs, pcnt_pkw hw h32, Nat.zero_add]
    simp only [one_mul]
  rewrite [enum_eq, hlv, sum_products_slices _ rest 1 22 T0 hT0,
    List.map_congr_left fun j _ => hcnt j]
  rewrite [show List.range 22 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] from rfl,
    show List.map cntS
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] =
      [cntS 0, cntS 1, cntS 2, cntS 3, cntS 4, cntS 5, cntS 6, cntS 7, cntS 8, cntS 9, cntS 10,
        cntS 11, cntS 12, cntS 13, cntS 14, cntS 15, cntS 16, cntS 17, cntS 18, cntS 19, cntS 20,
        cntS 21] from rfl]
  rewrite [Nat.eq_of_beq_eq_true s0, Nat.eq_of_beq_eq_true s1, Nat.eq_of_beq_eq_true s2,
    Nat.eq_of_beq_eq_true s3, Nat.eq_of_beq_eq_true s4, Nat.eq_of_beq_eq_true s5,
    Nat.eq_of_beq_eq_true s6, Nat.eq_of_beq_eq_true s7, Nat.eq_of_beq_eq_true s8,
    Nat.eq_of_beq_eq_true s9, Nat.eq_of_beq_eq_true s10, Nat.eq_of_beq_eq_true s11,
    Nat.eq_of_beq_eq_true s12, Nat.eq_of_beq_eq_true s13, Nat.eq_of_beq_eq_true s14,
    Nat.eq_of_beq_eq_true s15, Nat.eq_of_beq_eq_true s16, Nat.eq_of_beq_eq_true s17,
    Nat.eq_of_beq_eq_true s18, Nat.eq_of_beq_eq_true s19, Nat.eq_of_beq_eq_true s20,
    Nat.eq_of_beq_eq_true s21]
  rfl

theorem counts : (ordW 22 [toTable m22gA, toTable m22gB, toTable m22gB] 5 = true)
    ∧ (pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
       (fun x y => pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) = 887040) := by
  have hw : (22 : Nat) ≤ 2 ^ 5 := by norm_num
  have h32 : (22 : Nat) < 2 ^ 32 := by norm_num
  obtain ⟨H, hHdef⟩ : ∃ H, H = m22Certificate.originalSubgroup := ⟨_, rfl⟩
  have hH : H = Subgroup.closure {g | g ∈ [m22gA, m22gB]} := by
    rw [hHdef, m22Certificate]
    exact certificate_originalSubgroup _ _ _ _ _
  have hA : m22gA ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (List.mem_cons_self ..)
  have hB : m22gB ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hoA := Nat.eq_of_beq_eq_true oA
  rw [I, ordTwo_pkw hw h32] at hoA
  have ordA : orderOf m22gA = 2 := of_ite_eq_one hoA
  have hoW := Nat.eq_of_beq_eq_true wAB
  rw [I, ordPr_pkw hw h32 Nat.prime_five] at hoW
  obtain ⟨L, hLdef⟩ : ∃ L, L = enumeration m22Certificate := ⟨_, rfl⟩
  have hnd : L.Nodup := by
    rw [hLdef, enum_eq]
    exact products_nodup_of_baseOK base
  have hsub : ∀ g ∈ L, g ∈ H := by
    rw [hLdef, hHdef, m22Certificate]
    exact certificate_enumeration_mem _ _ _ _ _
  have hLlen : L.length = 443520 := by
    rw [hLdef, enum_eq, length_products]
    exact Nat.eq_of_beq_eq_true lens
  have hcard : Nat.card H = 443520 := by
    have hset : {g | g ∈ [m22gA, m22gB]} = ({m22gA, m22gB} : Set (Equiv.Perm (Fin 22))) := by
      ext g
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff]
    rw [hH, hset, ← m22_eq]
    exact card_M22
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := mem_iff_of_nodup_card H hnd hsub (by rw [hcard, hLlen])
  obtain ⟨hX, hP⟩ := decode ordA hLlen (by rw [hLdef]; exact sum_cntW)
  have hpc : pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
      (fun x y => pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) =
      ((L.filter fun h => decide (orderOf h = 2)).map (partnersW L 4 ws)).sum := by
    rewrite [pairCount_spec (forall₂_orderTables h32 m22Certificate (by norm_num : 0 < 2))
      (forall₂_orderTables h32 m22Certificate (by norm_num : 0 < 4))
      (R := fun x y => WordsRel ws x y) ?_, List.map_reverse, List.sum_reverse, ← hLdef]
    · refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
      rewrite [List.countP_reverse, partnersW]
      rfl
    · intro x xg y yg hx hy hxg hyg
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hxg hyg
      exact pair_iff hx hy hxg.2 hyg.2
  have hpa : partnersW L 4 ws m22gA = 768 := by
    rewrite [partnersW, List.countP_filter, ← hP]
    exact congrArg L.countP (funext fun y => partner_iff m22gA y)
  have hclosed : ∀ c ∈ H, ∀ x ∈ L.filter (fun h => decide (orderOf h = 2)),
      c * x * c⁻¹ ∈ L.filter (fun h => decide (orderOf h = 2)) := by
    intro c hc x hx
    rw [List.mem_filter, decide_eq_true_eq, hmem] at hx ⊢
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx.1) (Subgroup.inv_mem _ hc),
      (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hx.2⟩
  have hr : m22gA ∈ L.filter (fun h => decide (orderOf h = 2)) :=
    List.mem_filter.2 ⟨(hmem _).2 hA, decide_eq_true ordA⟩
  obtain ⟨hcnd, hK⟩ : cl.Nodup ∧ ∀ k ∈ cl, ∃ c ∈ H, k = pkw 5 (c * m22gA * c⁻¹) := by
    rewrite [cl]
    exact conjDFS_mem_w hw h32 H hA hB 1200
  obtain ⟨hC, hm⟩ := upkw_conj hw hK
  have hndC : (cl.map (upkw 22 5)).Nodup :=
    List.Nodup.of_map (pkw 5) (by rw [hm]; exact hcnd)
  have hlC : (cl.map (upkw 22 5)).length = 1155 := by
    rw [List.length_map]
    exact Nat.eq_of_beq_eq_true ncl
  have hXlen : (L.filter fun h => decide (orderOf h = 2)).length = 1155 := by
    rw [← List.countP_eq_length_filter, hX]
  have hone := sum_eq_two_classes H (partnersW L 4 ws)
    (fun c hc x => partnersW_conj H L hnd hmem 4 ws hc x) _ hclosed hr hr hC
    (C₂ := []) (by simp) (by rw [List.append_nil]; exact hndC) (by rw [hXlen, hlC]; simp)
  refine ⟨ordW_gens (of_ite_eq_one hoW), ?_⟩
  rewrite [hpc, hone, hlC, hpa]
  rfl

end CertificateChecks.KernelSpor.M22Pair5

end
