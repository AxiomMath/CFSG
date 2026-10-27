
module

public import Certificates.Kernel.Parrott946.Glue17e

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] noncomputable def xI (j : ℕ) : P45 :=
  if h : j < 43 then Classical.choose (prep_iE h) else 1

theorem xI_spec {j : ℕ} (hj : j < 43) :
    PRep 45 6 (iE j) (xI j) ∧ xI j ∈ T0g ∧ xI j * xI j = 1 ∧ xI j ≠ 1 := by
  rw [xI, dif_pos hj]
  exact Classical.choose_spec (prep_iE hj)

set_option exponentiation.threshold 300 in
theorem iE_lt {j : ℕ} (hj : j < 43) : iE j < 2 ^ 270 := by
  rw [iE_eq hj]
  have h := allL_spec I_lt j (by rw [len_I]; exact hj)
  exact Nat.blt_eq.mp h

theorem I_nodup : D17.I.Nodup := (ltChainK_spec c17_inv.1).1.imp ne_of_lt

set_option exponentiation.threshold 300 in
theorem xI_inj {j k : ℕ} (hj : j < 43) (hk : k < 43) (e : xI j = xI k) : j = k := by
  have h1 := (xI_spec hj).1
  rw [e] at h1
  have h := prep_canon_eq h1 (xI_spec hk).1 (iE_lt hj) (iE_lt hk)
  rw [iE_eq hj, iE_eq hk, List.getD_eq_getElem _ _ (by rw [len_I]; exact hj),
    List.getD_eq_getElem _ _ (by rw [len_I]; exact hk)] at h
  exact (I_nodup.getElem_inj_iff).1 h

theorem eq_xI {j : ℕ} (hj : j < 43) {x : P45} (hx : PRep 45 6 (iE j) x) : x = xI j :=
  prep_eq hx (xI_spec hj).1

theorem comm_bit {j k : ℕ} (hj : j < 43) (hk : k < 43) (hb : bitB (D17.CM.getD j 0) k = true) :
    xI j * xI k = xI k * xI j := by
  have hc := cmK_spec c17_cm.1
  rw [hc.2 j (by rw [len_I]; exact hj), rowK_bit, ← iE_eq hj, ← iE_eq hk] at hb
  exact comm_of_cmm (xI_spec hj).1 (xI_spec hk).1 hb.2

theorem one_mem_prodSpan : ∀ gs : List P45, (1 : P45) ∈ prodSpan gs
  | [] => List.mem_singleton_self _
  | g :: gs => by
    rw [prodSpan_cons]
    exact List.mem_append_left _ (one_mem_prodSpan gs)

theorem f2_xI {js : List ℕ} (hjs : ∀ j ∈ js, j < 43) :
    List.Forall₂ (PRep 45 6) (mapK iE js) (js.map xI) := by
  rw [mapK_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun j hj => (xI_spec (hjs j hj)).1

theorem span_set {js : List ℕ} {m : ℕ} (hjs : ∀ j ∈ js, j < 43) (hspan : spanOK js m = true)
    (hm : m < 2 ^ 43) :
    ∀ x, x ∈ prodSpan (js.map xI) ↔ x = 1 ∨ ∃ j < 43, bitB m j = true ∧ x = xI j := by
  have hs := spanK_prep (f2_xI hjs)
  have hc := coverK_spec (Nat.eq_of_beq_eq_true hspan) hm len_I
  intro x
  constructor
  · intro hx
    obtain ⟨P, hP, hPx⟩ := f2_mem_right hs hx
    rcases hc.1 P hP with rfl | ⟨j, hj, hb, e⟩
    · exact Or.inl (prep_eq hPx prep_pid)
    · refine Or.inr ⟨j, hj, hb, eq_xI hj ?_⟩
      rw [iE_eq hj, e]
      exact hPx
  · rintro (rfl | ⟨j, hj, hb, rfl⟩)
    · exact one_mem_prodSpan _
    · obtain ⟨P, hP, e⟩ := hc.2 j hj hb
      obtain ⟨y, hy, hPy⟩ := f2_mem_left hs hP
      rw [e, ← iE_eq hj] at hPy
      rw [← eq_xI hj hPy]
      exact hy

theorem nodup_of_le {L : List P45} (h : L.length ≤ L.toFinset.card) : L.Nodup := by
  classical
  rw [List.card_toFinset] at h
  exact List.dedup_eq_self.1 ((List.dedup_sublist L).eq_of_length_le h)

theorem length_map_span (js : List ℕ) : (prodSpan (js.map xI)).length = 2 ^ js.length := by
  rw [length_prodSpan, List.length_map]

theorem e_group {js : List ℕ} {m : ℕ} (hjs : ∀ j ∈ js, j < 43)
    (hspan : spanOK js m = true) (hm : m < 2 ^ 43) (hcnt : cntN 43 (bitB m) = 15)
    (hlen : js.length = 4) (hcm : ∀ a ∈ js, ∀ b ∈ js, bitB (D17.CM.getD a 0) b = true) :
    ListGroupFacts (prodSpan (js.map xI)) (js.map xI) := by
  classical
  have hset := span_set hjs hspan hm
  have hsq : ∀ x ∈ js.map xI, x * x = 1 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact (xI_spec (hjs j hj)).2.2.1
  have hcomm : ∀ a ∈ js.map xI, ∀ b ∈ js.map xI, a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
    exact comm_bit (hjs j hj) (hjs k hk) (hcm j hj k hk)
  let H : Subgroup P45 := closure {x | x ∈ js.map xI}
  have hgH : ∀ g ∈ js.map xI, g ∈ H := fun g hg => subset_closure hg
  have hL : ∀ x, x ∈ prodSpan (js.map xI) ↔ x ∈ H := fun x =>
    ⟨fun hx => prodSpan_mem H hgH x hx,
      fun hx => mem_prodSpan_of_mem_closure _ hsq hcomm x hx⟩
  have hHA : H ≤ A := by
    rw [closure_le]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    exact T0g_le_A (xI_spec (hjs j hj)).2.1
  refine listFacts_of hL (nodup_of_le ?_) hgH hHA
  let F := (Finset.range 43).filter fun j => bitB m j = true
  have hF : F.card = 15 := by rw [← hcnt, cntN_eq]
  have hsub : insert (1 : P45) (F.image xI) ⊆ (prodSpan (js.map xI)).toFinset := by
    intro x hx
    rw [List.mem_toFinset, hset]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Or.inl rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_filter, Finset.mem_range] at hj
      exact Or.inr ⟨j, hj.1, hj.2, rfl⟩
  have hinj : Set.InjOn xI F := by
    intro j hj k hk e
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj hk
    exact xI_inj hj.1 hk.1 e
  have h1 : (1 : P45) ∉ F.image xI := by
    intro h
    obtain ⟨j, hj, e⟩ := Finset.mem_image.1 h
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact (xI_spec hj.1).2.2.2 e
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h1, Finset.card_image_of_injOn hinj, hF] at hc
  rw [length_map_span, hlen]
  exact hc

theorem cm_bits : (∀ a ∈ [6, 21, 31, 41], ∀ b ∈ [6, 21, 31, 41], bitB (D17.CM.getD a 0) b = true) ∧
    (∀ a ∈ [25, 21, 38, 41], ∀ b ∈ [25, 21, 38, 41], bitB (D17.CM.getD a 0) b = true) ∧
    (∀ a ∈ [11, 6, 41, 21], ∀ b ∈ [11, 6, 41, 21], bitB (D17.CM.getD a 0) b = true) ∧
    (∀ a ∈ [12, 14, 41, 21], ∀ b ∈ [12, 14, 41, 21], bitB (D17.CM.getD a 0) b = true) := by
  decide +kernel

theorem masks_lt : D17.M0 < 2 ^ 43 ∧ D17.M1 < 2 ^ 43 ∧ D17.M2 < 2 ^ 43 ∧ D17.M3 < 2 ^ 43 := by
  decide +kernel

theorem gens_eq : Sgens = [6, 21, 31, 41].map xI ∧ E3gens = [25, 21, 38, 41].map xI ∧
    E1gens = [11, 6, 41, 21].map xI ∧ E2gens = [12, 14, 41, 21].map xI := by
  obtain ⟨g6, g21, g31, g41, g25, g38, g11, g12, g14⟩ := c17_gens
  have e6 : u = xI 6 := eq_xI (by norm_num) (by rw [g6]; exact prep_u)
  have e21 : alpha1 * alpha2 = xI 21 := eq_xI (by norm_num) (by rw [g21]; exact prep_pc prep_a1 prep_a2)
  have e31 : beta1 * beta2 = xI 31 := eq_xI (by norm_num) (by rw [g31]; exact prep_pc prep_b1 prep_b2)
  have e41 : t = xI 41 := eq_xI (by norm_num) (by rw [g41]; exact prep_t)
  have e25 : u * v = xI 25 := eq_xI (by norm_num) (by rw [g25]; exact prep_uv)
  have e38 : alpha1 * beta1 * beta2 = xI 38 :=
    eq_xI (by norm_num) (by rw [g38]; exact prep_pc (prep_pc prep_a1 prep_b1) prep_b2)
  have e11 : v = xI 11 := eq_xI (by norm_num) (by rw [g11]; exact prep_v)
  have e12 : v * alpha1 = xI 12 := eq_xI (by norm_num) (by rw [g12]; exact prep_pc prep_v prep_a1)
  have e14 : u * beta1 * beta2 = xI 14 :=
    eq_xI (by norm_num) (by rw [g14]; exact prep_pc (prep_pc prep_u prep_b1) prep_b2)
  simp only [Sgens, E3gens, E1gens, E2gens, List.map_cons, List.map_nil]
  rw [e25, e38, e14, e12, e21, e31, e6, e41, e11]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem mem43 {js : List ℕ} (h : js.all (fun j => decide (j < 43)) = true) : ∀ j ∈ js, j < 43 :=
  fun j hj => of_decide_eq_true (List.all_eq_true.1 h j hj)

theorem s_group : ListGroupFacts (Slist ()) Sgens := by
  rw [Slist, tabList_eq, tabList_eq, gens_eq.1]
  exact e_group (mem43 (by decide)) c17_spans.1 masks_lt.1 c17_masks.1 rfl cm_bits.1

theorem e3_group : ListGroupFacts (E3list ()) E3gens := by
  rw [E3list, tabList_eq, tabList_eq, gens_eq.2.1]
  exact e_group (mem43 (by decide)) c17_spans.2.1 masks_lt.2.1 c17_masks.2.1 rfl cm_bits.2.1

theorem e1_group : ListGroupFacts (E1list ()) E1gens := by
  rw [E1list, tabList_eq, tabList_eq, gens_eq.2.2.1]
  exact e_group (mem43 (by decide)) c17_spans.2.2.1 masks_lt.2.2.1 c17_masks.2.2.1 rfl
    cm_bits.2.2.1

theorem e2_group : ListGroupFacts (E2list ()) E2gens := by
  rw [E2list, tabList_eq, tabList_eq, gens_eq.2.2.2]
  exact e_group (mem43 (by decide)) c17_spans.2.2.2 masks_lt.2.2.2 c17_masks.2.2.2.1 rfl
    cm_bits.2.2.2

end CertificateChecks.Parrott946

end
