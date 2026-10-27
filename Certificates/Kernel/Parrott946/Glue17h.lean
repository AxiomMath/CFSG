
module

public import Certificates.Kernel.Parrott946.Glue17g

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem bitB_iff (m k : ℕ) : bitB m k = true ↔ m.testBit k = true := by
  unfold bitB
  rw [Nat.blt_eq]
  change 0 < m &&& 1 <<< k ↔ _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  constructor
  · intro h
    by_contra hb
    rw [Bool.not_eq_true] at hb
    have h0 : m &&& 2 ^ k = 0 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : k = i
      · subst hi
        rw [hb]
        rfl
      · simp [hi]
    omega
  · intro h
    have h1 : (m &&& 2 ^ k).testBit k = true := by
      rw [Nat.testBit_and, h, Nat.testBit_two_pow_self]
      rfl
    have := Nat.ge_two_pow_of_testBit h1
    have := Nat.two_pow_pos k
    omega

theorem idx_I {j : ℕ} (hj : j < 43) :
    ∃ i < 128, T0Z.T i = iE j ∧ isInvK 45 6 (T0Z.T i) = true := by
  have h := allL_spec c17_inv.2.2.2.1 j (by rw [len_I]; exact hj)
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨i, hi, e⟩ := memK_spec h.2
  rw [← iE_eq hj] at e h
  exact ⟨i, hi, e, by rw [e]; exact h.1⟩

theorem inv_eq_xI {c : P45} (hc : c ∈ T0g) (h2 : c * c = 1) (h1 : c ≠ 1) :
    ∃ j < 43, c = xI j := by
  classical
  obtain ⟨e, he, hall, -⟩ := t0_enum
  let idx : ℕ → ℕ := fun j => if h : j < 43 then Classical.choose (idx_I h) else 0
  have hidx : ∀ j < 43, idx j < 128 ∧ T0Z.T (idx j) = iE j ∧ isInvK 45 6 (T0Z.T (idx j)) = true :=
    fun j hj => by
      simp only [idx, dif_pos hj]
      exact Classical.choose_spec (idx_I hj)
  let F := (Finset.range 128).filter fun i => isInvK 45 6 (T0Z.T i) = true
  have hF : F.card = 43 := by rw [← c17_inv.2.2.2.2, cntN_eq]
  have himg : (Finset.range 43).image idx ⊆ F := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(hidx j hj).1, (hidx j hj).2.2⟩
  have hinj : Set.InjOn idx (Finset.range 43) := by
    intro j hj k hk ejk
    rw [Finset.mem_coe, Finset.mem_range] at hj hk
    apply xI_inj hj hk
    have h1' := (xI_spec hj).1
    have h2' := (xI_spec hk).1
    rw [← (hidx j hj).2.1] at h1'
    rw [← (hidx k hk).2.1, ← ejk] at h2'
    exact prep_eq h1' h2'
  have heq : (Finset.range 43).image idx = F :=
    Finset.eq_of_subset_of_card_le himg (by rw [hF, Finset.card_image_of_injOn hinj,
      Finset.card_range])
  obtain ⟨i, hi, rfl⟩ := hall c hc
  have hiF : i ∈ F := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hi, (inv_iff_isInvK (he i hi).1).2 ⟨h2, h1⟩⟩
  rw [← heq] at hiF
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hiF
  rw [Finset.mem_range] at hj
  refine ⟨j, hj, eq_xI hj ?_⟩
  rw [← (hidx j hj).2.1]
  exact (he _ (hidx j hj).1).1

theorem rows_lt : ∀ c ∈ D17.CM, c < 2 ^ 43 := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hc
  have hcm := cmK_spec c17_cm.1
  have ha' : a < D17.I.length := by rw [← hcm.1]; exact ha
  rw [← List.getD_eq_getElem _ 0 ha, hcm.2 a ha', ← len_I]
  exact rowK_lt

theorem lane_CMT {a : ℕ} (ha : a < 43) : lane 43 D17.CMT a = D17.CM.getD a 0 := by
  rw [← c17_cm.2]
  refine lane_packL rows_lt ?_
  rw [(cmK_spec c17_cm.1).1, len_I]
  exact ha

theorem bit_of_comm {a j : ℕ} (ha : a < 43) (hj : j < 43) (h : xI a * xI j = xI j * xI a) :
    bitB (lane 43 D17.CMT a) j = true := by
  rw [lane_CMT ha, (cmK_spec c17_cm.1).2 a (by rw [len_I]; exact ha), rowK_bit, len_I,
    ← iE_eq ha, ← iE_eq hj]
  exact ⟨hj, eq22_of_mul17 (xI_spec ha).1 (xI_spec hj).1 (xI_spec hj).1 (xI_spec ha).1 h⟩

@[expose] noncomputable def andRows (js : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) (Nat.sub (Nat.shiftLeft 1 43) 1)
    (fun j _ ih => Nat.land (lane 43 D17.CMT j) ih) js

theorem andRows_bit {j : ℕ} (hj : j < 43) : ∀ {js : List ℕ},
    (∀ a ∈ js, bitB (lane 43 D17.CMT a) j = true) → (andRows js).testBit j = true
  | [], _ => by
    change (Nat.sub (Nat.shiftLeft 1 43) 1).testBit j = true
    have e : Nat.sub (Nat.shiftLeft 1 43) 1 = 2 ^ 43 - 1 := by decide
    rw [e, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hj
  | a :: js, h => by
    change (Nat.land (lane 43 D17.CMT a) (andRows js)).testBit j = true
    have e : Nat.land (lane 43 D17.CMT a) (andRows js) = lane 43 D17.CMT a &&& andRows js := rfl
    rw [e, Nat.testBit_and, (bitB_iff _ _).1 (h a List.mem_cons_self),
      andRows_bit hj fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem mask_bit_of_cent {js : List ℕ} {m : ℕ} (hc : centOK js m = true) {j : ℕ} (hj : j < 43)
    (h : ∀ a ∈ js, bitB (lane 43 D17.CMT a) j = true) : bitB m j = true := by
  unfold centOK at hc
  rw [strictB_eq'] at hc
  have e := Nat.eq_of_beq_eq_true hc
  have hb := andRows_bit hj h
  change (andRows js).testBit j = true at hb
  rw [bitB_iff]
  have e' : andRows js &&& m = andRows js := e
  rw [← e', Nat.testBit_and, Bool.and_eq_true] at hb
  exact hb.2

theorem inv_cent {js : List ℕ} {m : ℕ} (hjs : ∀ j ∈ js, j < 43)
    (hspan : spanOK js m = true) (hm : m < 2 ^ 43) (hc : centOK js m = true) :
    invCentralizerB (T0list ()) (js.map xI) (prodSpan (js.map xI)) = true := by
  have hset := span_set hjs hspan hm
  unfold invCentralizerB
  refine List.all_eq_true.2 fun c hcT => ?_
  rw [Bool.or_eq_true]
  by_cases hcond : c * c = 1 ∧ ∀ x ∈ js.map xI, c * x = x * c
  · refine Or.inr (decide_eq_true ((hset c).2 ?_))
    by_cases h1 : c = 1
    · exact Or.inl h1
    · obtain ⟨j, hj, rfl⟩ := inv_eq_xI ((t0_set c).1 hcT) hcond.1 h1
      refine Or.inr ⟨j, hj, mask_bit_of_cent hc hj fun a ha => ?_, rfl⟩
      exact bit_of_comm (hjs a ha) hj (hcond.2 (xI a) (List.mem_map_of_mem ha)).symm
  · refine Or.inl ?_
    rw [Bool.not_eq_true', Bool.and_eq_false_iff]
    by_cases h2 : c * c = 1
    · refine Or.inr ?_
      rw [Bool.eq_false_iff]
      intro hall
      exact hcond ⟨h2, fun x hx => of_decide_eq_true (List.all_eq_true.1 hall x hx)⟩
    · exact Or.inl (decide_eq_false h2)

theorem e16_centralizer : e16CentralizerCheck () = true := by
  unfold e16CentralizerCheck
  rw [tabList_eq, tabList_eq, tabList_eq, tabList_eq, Slist, E3list, E1list, E2list, tabList_eq,
    tabList_eq, tabList_eq, tabList_eq, tabList_eq, tabList_eq, tabList_eq, tabList_eq,
    gens_eq.1, gens_eq.2.1, gens_eq.2.2.1, gens_eq.2.2.2]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨inv_cent (mem43 (by decide)) c17_spans.1 masks_lt.1 c17_ecent.1,
    inv_cent (mem43 (by decide)) c17_spans.2.1 masks_lt.2.1 c17_ecent.2.1⟩,
    inv_cent (mem43 (by decide)) c17_spans.2.2.1 masks_lt.2.2.1 c17_ecent.2.2.1⟩,
    inv_cent (mem43 (by decide)) c17_spans.2.2.2 masks_lt.2.2.2 c17_ecent.2.2.2⟩

end CertificateChecks.Parrott946

end
