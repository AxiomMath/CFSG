module

public import Certificates.Kernel.Sporadic.M12Count

public section

namespace CertificateChecks.KernelSpor.M12Count

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt CFSG.Sporadic.Th

private theorem split4 {α : Type*} (l : List α) (hl : l.length ≤ 12) :
    l = l.take 3 ++ ((l.drop 3).take 3 ++ ((l.drop 6).take 3 ++ (l.drop 9).take 3)) := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · intro i h₁ h₂
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.length_take,
      List.length_drop]
    split_ifs <;> congr 1 <;> omega

private theorem partners_eq (L : List (Equiv.Perm (Fin 12))) (x : Equiv.Perm (Fin 12)) :
    partners L 3 11 6 x = L.countP fun y =>
      decide (orderOf y = 3 ∧ orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6) := by
  rw [partners, List.countP_filter]
  refine List.countP_congr fun y _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  unfold PartnerRel
  tauto

private theorem sum_cnt4 :
    ((enumeration m12Certificate).map fun h =>
      cnt4 12 4 (mask 4) (pk (1 : Equiv.Perm (Fin 12))) (pk m12gA) (pk r₂) (pk h)).sum =
      212137649207852925225 + 119903955227500347590 + 119903942033360814278 +
        101457197959651262662 := by
  have hn : (12 : Nat) ≤ 16 := by norm_num
  obtain ⟨T0, rest, hlv⟩ : ∃ T0 rest, lv = T0 :: rest := by
    cases h : lv with
    | nil =>
      have := Nat.eq_of_beq_eq_true lens
      rw [h] at this
      simp at this
    | cons T0 rest => exact ⟨T0, rest, rfl⟩
  have hT0 : T0.length ≤ 12 := by
    have := Nat.le_of_ble_eq_true len₀
    rw [hlv] at this
    simpa using this
  have hcnt : ∀ j, cntS j = ((products (((T0.drop (3 * j)).take 3) :: rest)).map fun h =>
      cnt4 12 4 (mask 4) (pk (1 : Equiv.Perm (Fin 12))) (pk m12gA) (pk r₂) (pk h)).sum := by
    intro j
    have hs : slice j = ((T0.drop (3 * j)).take 3) :: rest := by rw [slice, hlv]; rfl
    rw [cntS, I, ← hs, pcnt_pk hn, Nat.zero_add]
    simp only [one_mul]
  have e0 := hcnt 0
  have e1 := hcnt 1
  have e2 := hcnt 2
  have e3 := hcnt 3
  simp only [Nat.reduceMul, List.drop_zero] at e0 e1 e2 e3
  have hL : enumeration m12Certificate = products lv := rfl
  rw [hL, hlv, split4 T0 hT0, products_append_head, products_append_head, products_append_head]
  simp only [List.map_append, List.sum_append]
  rw [← e0, ← e1, ← e2, ← e3]
  have v0 := Nat.eq_of_beq_eq_true s0
  have v1 := Nat.eq_of_beq_eq_true s1
  have v2 := Nat.eq_of_beq_eq_true s2
  have v3 := Nat.eq_of_beq_eq_true s3
  omega

theorem counts : (m12Certificate.check = true)
    ∧ (ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
      pairTest 12 11 6 2 3 (toTable m12gA) (toTable m12gB) = true)
    ∧ ((orderTables m12Certificate 2).length = 891 ∧
      (orderTables m12Certificate 3).length = 4400)
    ∧ (pairCount (orderTables m12Certificate 2) (orderTables m12Certificate 3)
      (pairTest 12 11 6 2 3) = 380160) := by
  have hn : (12 : Nat) ≤ 16 := by norm_num
  have hH : m12Certificate.originalSubgroup = Subgroup.closure {g | g ∈ [m12gA, m12gB]} :=
    certificate_originalSubgroup _ _ _ _ _
  have hA : m12gA ∈ m12Certificate.originalSubgroup := by
    rw [hH]; exact Subgroup.subset_closure (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := by
    rw [hH]; exact Subgroup.subset_closure (by simp)
  have hR : r₂ ∈ m12Certificate.originalSubgroup :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hA hB) 3) hB) 3
  have hoA := Nat.eq_of_beq_eq_true oA
  rw [I, ordTwo_pk hn] at hoA
  have ordA : orderOf m12gA = 2 := of_ite_eq_one hoA
  have hoR := Nat.eq_of_beq_eq_true oR
  rw [I, ordTwo_pk hn] at hoR
  have ordR : orderOf r₂ = 2 := of_ite_eq_one hoR
  have hpAB := Nat.eq_of_beq_eq_true pAB
  rw [I, partner_pk hn ordA] at hpAB
  obtain ⟨ordB, ordAB, ordC⟩ := of_ite_eq_one hpAB
  have hrepA := rep_toTable (by norm_num) m12gA
  have hrepB := rep_toTable (by norm_num) m12gB
  have wA : ordTest 12 2 (toTable m12gA) = true :=
    (ordTest_iff perm_faithful hrepA (by norm_num)).2 ordA
  have wB : ordTest 12 3 (toTable m12gB) = true :=
    (ordTest_iff perm_faithful hrepB (by norm_num)).2 ordB
  have wAB : pairTest 12 11 6 2 3 (toTable m12gA) (toTable m12gB) = true :=
    (pairTest_iff perm_faithful hrepA hrepB (by norm_num) (by norm_num) ordA ordB (by norm_num)
      (by norm_num)).2 ⟨ordAB, ordC⟩
  have hQ : ValidSchreier m12Certificate := check
  have hL : (enumeration m12Certificate).Nodup := enumeration_nodup _ hQ
  have hmem : ∀ g, g ∈ enumeration m12Certificate ↔ g ∈ m12Certificate.originalSubgroup :=
    mem_enumeration_iff _ hQ
  have hLlen : (enumeration m12Certificate).length = 95040 := by
    have h := Nat.eq_of_beq_eq_true lens
    rw [lv] at h
    rw [enumeration, length_products]
    exact h
  have hdec := sum_cnt4
  rw [List.map_congr_left fun h _ => cnt4_pk hn ordA ordR h] at hdec
  simp only [List.sum_map_add, List.sum_map_mul_left, sum_ite_eq_countP] at hdec
  have hAle := (List.countP_le_length (p := fun h => decide (orderOf h = 2))
    (l := enumeration m12Certificate))
  have hBle := (List.countP_le_length (p := fun h => decide (orderOf h = 3))
    (l := enumeration m12Certificate))
  have hCle := (List.countP_le_length (p := fun y => decide (orderOf y = 3 ∧
    orderOf (m12gA * y) = 11 ∧ orderOf (m12gA * y * m12gA⁻¹ * y⁻¹) = 6))
    (l := enumeration m12Certificate))
  have hDle := (List.countP_le_length (p := fun y => decide (orderOf y = 3 ∧
    orderOf (r₂ * y) = 11 ∧ orderOf (r₂ * y * r₂⁻¹ * y⁻¹) = 6))
    (l := enumeration m12Certificate))
  rw [hLlen] at hAle hBle hCle hDle
  have hA891 : (enumeration m12Certificate).countP (fun h => decide (orderOf h = 2)) = 891 := by
    omega
  have hB4400 : (enumeration m12Certificate).countP (fun h => decide (orderOf h = 3)) = 4400 := by
    omega
  have hC384 : (enumeration m12Certificate).countP (fun y => decide (orderOf y = 3 ∧
      orderOf (m12gA * y) = 11 ∧ orderOf (m12gA * y * m12gA⁻¹ * y⁻¹) = 6)) = 384 := by
    omega
  have hD480 : (enumeration m12Certificate).countP (fun y => decide (orderOf y = 3 ∧
      orderOf (r₂ * y) = 11 ∧ orderOf (r₂ * y * r₂⁻¹ * y⁻¹) = 6)) = 480 := by
    omega
  have hlen : ∀ m, 0 < m → (orderTables m12Certificate m).length =
      (enumeration m12Certificate).countP fun h => decide (orderOf h = m) := by
    intro m hm
    rw [(forall₂_orderTables (by norm_num) m12Certificate hm).length_eq, List.length_reverse,
      List.countP_eq_length_filter]
  have hcoe : ∀ p : m12Certificate.originalSubgroup × m12Certificate.originalSubgroup,
      (orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6) ↔
      (orderOf (p.1 : Equiv.Perm (Fin 12)) = 2 ∧ orderOf (p.2 : Equiv.Perm (Fin 12)) = 3 ∧
        PartnerRel 11 6 (p.1 : Equiv.Perm (Fin 12)) p.2) := fun p => by
    simp only [PartnerRel, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  have hcard : Nat.card {p : m12Certificate.originalSubgroup × m12Certificate.originalSubgroup //
      orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6} =
      (((enumeration m12Certificate).filter fun h => decide (orderOf h = 2)).map
        (partners (enumeration m12Certificate) 3 11 6)).sum := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
      card_pairs_eq_sum m12Certificate.originalSubgroup (enumeration m12Certificate) hL hmem
        (fun h => orderOf h = 2) (fun h => orderOf h = 3) (PartnerRel 11 6)]
    rfl
  have hclosed : ∀ c ∈ m12Certificate.originalSubgroup,
      ∀ x ∈ (enumeration m12Certificate).filter (fun h => decide (orderOf h = 2)),
        c * x * c⁻¹ ∈ (enumeration m12Certificate).filter (fun h => decide (orderOf h = 2)) := by
    intro c hc x hx
    rw [List.mem_filter, decide_eq_true_eq, hmem] at hx ⊢
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx.1) (Subgroup.inv_mem _ hc),
      (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hx.2⟩
  have hr₁ : m12gA ∈ (enumeration m12Certificate).filter (fun h => decide (orderOf h = 2)) :=
    List.mem_filter.2 ⟨(hmem _).2 hA, decide_eq_true ordA⟩
  have hr₂ : r₂ ∈ (enumeration m12Certificate).filter (fun h => decide (orderOf h = 2)) :=
    List.mem_filter.2 ⟨(hmem _).2 hR, decide_eq_true ordR⟩
  have hK₁ := conjTreeP_mem hn m12Certificate.originalSubgroup hA hB t₁
  have hK₂ := conjTreeP_mem hn m12Certificate.originalSubgroup hA hB t₂
  obtain ⟨hC₁, hm₁⟩ := upk_conj hn hK₁
  obtain ⟨hC₂, hm₂⟩ := upk_conj hn hK₂
  have hnd : (cl₁.1.map (upk 12) ++ cl₂.1.map (upk 12)).Nodup :=
    List.Nodup.of_map pk (by rw [List.map_append, hm₁, hm₂]; exact nodup_of_distB dist)
  have hn₁ := Nat.eq_of_beq_eq_true n₁
  have hn₂ := Nat.eq_of_beq_eq_true n₂
  have hl₁ : (cl₁.1.map (upk 12)).length = 495 := by rw [List.length_map, hn₁]
  have hl₂ : (cl₂.1.map (upk 12)).length = 396 := by rw [List.length_map, hn₂]
  have hXGlen : ((enumeration m12Certificate).filter fun h => decide (orderOf h = 2)).length =
      891 := by
    rw [← List.countP_eq_length_filter, hA891]
  have htwo := sum_eq_two_classes m12Certificate.originalSubgroup
    (partners (enumeration m12Certificate) 3 11 6)
    (fun c hc x => partners_conj m12Certificate.originalSubgroup (enumeration m12Certificate) hL
      hmem 3 11 6 hc x) _ hclosed hr₁ hr₂ hC₁ hC₂ hnd (by rw [hXGlen, hl₁, hl₂])
  have hpart := partners_eq (enumeration m12Certificate)
  refine ⟨check, ⟨wA, wB, wAB⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hlen 2 (by norm_num)]
    exact hA891
  · rw [hlen 3 (by norm_num)]
    exact hB4400
  · rw [← card_image_pairs_eq (by norm_num) m12Certificate hQ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), hcard, htwo, hl₁, hl₂, hpart, hpart]
    omega

end CertificateChecks.KernelSpor.M12Count

end
