
module

public import Certificates.Kernel.Parrott946.Glue17l

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

theorem pairwiseComm_all : ∀ {l : List P45}, pairwiseCommB l = true →
    ∀ a ∈ l, ∀ b ∈ l, a * b = b * a
  | [], _, a, ha, _, _ => absurd ha (by simp)
  | x :: l, h, a, ha, b, hb => by
    simp only [pairwiseCommB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · rw [ha']
      exact h.1 b hb'
    · rw [hb']
      exact (h.1 a ha').symm
    · exact pairwiseComm_all h.2 a ha' b hb'

theorem prodSpan_mem_set (P : P45 → Prop) (h1 : P 1) (hmul : ∀ x y, P x → P y → P (x * y)) :
    ∀ {gs : List P45}, (∀ g ∈ gs, P g) → ∀ x ∈ prodSpan gs, P x
  | [], _, x, hx => by
    have e : x = 1 := by simpa [prodSpan] using hx
    rw [e]
    exact h1
  | g :: gs, hg, x, hx => by
    rw [prodSpan_cons, List.mem_append, List.mem_map] at hx
    have ih := prodSpan_mem_set P h1 hmul (gs := gs) fun y hy => hg y (List.mem_cons_of_mem g hy)
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih x hx
    · exact hmul _ _ (hg g List.mem_cons_self) (ih y hy)

theorem len_le_of_sub {L : List P45} {X : Finset P45} (hn : L.Nodup) (h : ∀ x ∈ L, x ∈ X) :
    L.length ≤ X.card := by
  classical
  rw [← List.toFinset_card_of_nodup hn]
  exact Finset.card_le_card fun x hx => h x (List.mem_toFinset.1 hx)

@[expose] noncomputable def maskSet (m : ℕ) : Finset P45 :=
  insert 1 (((Finset.range 43).filter fun j => bitB m j = true).image xI)

theorem mem_maskSet {m : ℕ} {x : P45} :
    x ∈ maskSet m ↔ x = 1 ∨ ∃ j < 43, bitB m j = true ∧ x = xI j := by
  unfold maskSet
  rw [Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (h | ⟨j, ⟨hj, hb⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hb, rfl⟩
  · rintro (h | ⟨j, hj, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, ⟨hj, hb⟩, rfl⟩

theorem card_maskSet {m : ℕ} (h : cntN 43 (bitB m) = 7) : (maskSet m).card ≤ 8 := by
  classical
  unfold maskSet
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_image_le (s := (Finset.range 43).filter fun j => bitB m j = true) (f := xI)
  rw [← cntN_eq, h] at this
  omega

theorem maskSet_mul {m : ℕ} (hc : closedK 45 6 D17.I m (pidn 45 6) = true) {x y : P45}
    (hx : x ∈ maskSet m) (hy : y ∈ maskSet m) : x * y ∈ maskSet m := by
  rcases mem_maskSet.1 hx with rfl | ⟨a, ha, hba, rfl⟩
  · rwa [one_mul]
  rcases mem_maskSet.1 hy with rfl | ⟨b, hb, hbb, rfl⟩
  · rwa [mul_one]
  have h := closedK_spec hc (by rw [len_I]; exact ha) (by rw [len_I]; exact hb) hba hbb
  rw [← iE_eq ha, ← iE_eq hb] at h
  have hp : PRep 45 6 (pcomp 45 6 (mask 6) (iE a) (iE b)) (xI a * xI b) :=
    prep_pc (xI_spec ha).1 (xI_spec hb).1
  rcases inMaskK_spec h with e | ⟨j, hj, hbj, e⟩
  · rw [e] at hp
    exact mem_maskSet.2 (Or.inl (prep_eq hp prep_pid))
  · rw [len_I] at hj
    rw [← e, ← iE_eq hj] at hp
    exact mem_maskSet.2 (Or.inr ⟨j, hj, hbj, prep_eq hp (xI_spec hj).1⟩)

open Classical in
@[expose] noncomputable def jOf (x : P45) : ℕ :=
  if h : ∃ j < 43, x = xI j then Classical.choose h else 0

theorem jOf_spec {x : P45} (hx : x ∈ T0g) (h2 : x * x = 1) (h1 : x ≠ 1) :
    jOf x < 43 ∧ x = xI (jOf x) := by
  have h := inv_eq_xI hx h2 h1
  rw [jOf, dif_pos h]
  exact Classical.choose_spec h

theorem mem_invs {x : P45} (hx : x ∈ involutionsOf (T0list ())) :
    x ∈ T0g ∧ x * x = 1 ∧ x ≠ 1 := by
  unfold involutionsOf at hx
  rw [List.mem_filter, decide_eq_true_eq] at hx
  exact ⟨(t0_set x).1 hx.1, hx.2⟩

theorem span_dup {l : List P45} (hl : l.length = 4) (hinv : ∀ x ∈ l, x * x = 1)
    (hcomm : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a) (hn : ¬ l.Nodup) : ¬ (prodSpan l).Nodup := by
  classical
  intro hsp
  have hd : l.dedup.length ≤ 3 := by
    by_contra h
    apply hn
    have h4 : l.length ≤ l.dedup.length := by omega
    exact List.dedup_eq_self.1 ((List.dedup_sublist l).eq_of_length_le h4)
  let H : Subgroup P45 := closure {x | x ∈ l}
  have hsub : ∀ x ∈ prodSpan l, x ∈ (prodSpan l.dedup).toFinset := by
    intro x hx
    have hxH := prodSpan_mem H (fun g hg => subset_closure hg) x hx
    have e : {x | x ∈ l} = {x | x ∈ l.dedup} := by
      ext y
      simp [List.mem_dedup]
    rw [List.mem_toFinset]
    refine mem_prodSpan_of_mem_closure _ (fun y hy => hinv y (List.mem_dedup.1 hy))
      (fun a ha b hb => hcomm a (List.mem_dedup.1 ha) b (List.mem_dedup.1 hb)) x ?_
    change x ∈ closure {x | x ∈ l.dedup}
    rw [← e]
    exact hxH
  have h1 := len_le_of_sub hsp hsub
  have h2 := List.toFinset_card_le (prodSpan l.dedup)
  rw [length_prodSpan, hl] at h1
  rw [length_prodSpan] at h2
  have : 2 ^ l.dedup.length ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hd
  omega

theorem lane_sym {a b : ℕ} (ha : a < 43) (hb : b < 43) (h : xI a * xI b = xI b * xI a) :
    bitB (lane 43 D17.CMT a) b = true := bit_of_comm ha hb h

theorem e16_in_t0 : e16Check () = true := by
  classical
  unfold e16Check
  refine List.all_eq_true.2 fun l hl => ?_
  rw [List.mem_sublistsLen] at hl
  obtain ⟨hsl, hlen⟩ := hl
  have hmem : ∀ x ∈ l, x ∈ T0g ∧ x * x = 1 ∧ x ≠ 1 := fun x hx => mem_invs (hsl.subset hx)
  rw [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hpc : pairwiseCommB l = true
  · refine Or.inr ?_
    have hcomm := pairwiseComm_all hpc
    rw [tabList_eq]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases hsp : (prodSpan l).Nodup
    ·
      have hnd : l.Nodup := by
        by_contra hn
        exact span_dup hlen (fun x hx => (hmem x hx).2.1) hcomm hn hsp
      let p : Fin 4 → ℕ := fun i => jOf (l[i.1]'(by rw [hlen]; exact i.2))
      have hpx : ∀ i : Fin 4, p i < 43 ∧ l[i.1]'(by rw [hlen]; exact i.2) = xI (p i) := fun i =>
        jOf_spec (hmem _ (List.getElem_mem _)).1 (hmem _ (List.getElem_mem _)).2.1
          (hmem _ (List.getElem_mem _)).2.2
      have hp : Function.Injective p := by
        intro i j e
        have e' : l[i.1]'(by rw [hlen]; exact i.2) = l[j.1]'(by rw [hlen]; exact j.2) := by
          rw [(hpx i).2, (hpx j).2, e]
        exact Fin.ext ((hnd.getElem_inj_iff).1 e')
      obtain ⟨m, hm, hbits⟩ := cliqueK_spec' c17_clique hp (fun i => (hpx i).1) fun i j hij => by
        refine lane_sym (hpx i).1 (hpx j).1 ?_
        rw [← (hpx i).2, ← (hpx j).2]
        exact hcomm _ (List.getElem_mem _) _ (List.getElem_mem _)
      have hinm : ∀ x ∈ l, ∃ j < 43, bitB m j = true ∧ x = xI j := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
        have hi4 : i < 4 := by rw [← hlen]; exact hi
        exact ⟨p ⟨i, hi4⟩, (hpx ⟨i, hi4⟩).1, hbits ⟨i, hi4⟩, (hpx ⟨i, hi4⟩).2⟩
      have hsmall : ∀ {m' : ℕ}, cntN 43 (bitB m') = 7 → closedK 45 6 D17.I m' (pidn 45 6) = true →
          m = m' → False := by
        intro m' hc hcl e
        subst e
        have hX : ∀ x ∈ prodSpan l, x ∈ maskSet m := prodSpan_mem_set (· ∈ maskSet m)
          (mem_maskSet.2 (Or.inl rfl)) (fun _ _ hx hy => maskSet_mul hcl hx hy)
          (fun x hx => mem_maskSet.2 (Or.inr (hinm x hx)))
        have h1 := len_le_of_sub hsp hX
        rw [length_prodSpan, hlen] at h1
        have h2 := card_maskSet hc
        omega
      have hbig : ∀ {js : List ℕ} {m' : ℕ}, (∀ j ∈ js, j < 43) → spanOK js m' = true →
          m' < 2 ^ 43 → cntN 43 (bitB m') = 15 → js.length = 4 →
          (∀ a ∈ js, ∀ b ∈ js, bitB (D17.CM.getD a 0) b = true) → m = m' →
          subsetB (prodSpan l) (prodSpan (js.map xI)) = true := by
        intro js m' hjs hspan hm' hcnt hl4 hcm e
        subst e
        have hG := e_group hjs hspan hm' hcnt hl4 hcm
        have hset := span_set hjs hspan hm'
        refine List.all_eq_true.2 fun x hx => decide_eq_true ?_
        refine prodSpan_mem_set (· ∈ prodSpan (js.map xI)) hG.one_mem
          (fun a b ha hb => of_decide_eq_true
            (List.all_eq_true.1 (List.all_eq_true.1 hG.mul_closed a ha) b hb))
          (fun y hy => (hset y).2 (Or.inr (hinm y hy))) x hx
      simp only [Ms, List.mem_cons, List.not_mem_nil, or_false] at hm
      have m4 := c17_masks.2.2.2.2.1
      have m5 := c17_masks.2.2.2.2.2.1
      have m6 := c17_masks.2.2.2.2.2.2.1
      have m7 := c17_masks.2.2.2.2.2.2.2.1
      have hcl := c17_masks.2.2.2.2.2.2.2.2
      rw [strictB_eq'] at hcl
      simp only [Bool.and_eq_true] at hcl
      rw [Slist, E3list, E1list, E2list, tabList_eq, tabList_eq, tabList_eq, tabList_eq,
        tabList_eq, tabList_eq, tabList_eq, tabList_eq, gens_eq.1, gens_eq.2.1, gens_eq.2.2.1,
        gens_eq.2.2.2]
      rcases hm with e | e | e | e | e | e | e | e
      · exact Or.inl (Or.inl (Or.inl (Or.inr (hbig (mem43 (by decide)) c17_spans.1 masks_lt.1
          c17_masks.1 rfl cm_bits.1 e))))
      · exact Or.inl (Or.inl (Or.inr (hbig (mem43 (by decide)) c17_spans.2.1
          masks_lt.2.1 c17_masks.2.1 rfl cm_bits.2.1 e)))
      · exact Or.inl (Or.inr (hbig (mem43 (by decide)) c17_spans.2.2.1 masks_lt.2.2.1
          c17_masks.2.2.1 rfl cm_bits.2.2.1 e))
      · exact Or.inr (hbig (mem43 (by decide)) c17_spans.2.2.2 masks_lt.2.2.2
          c17_masks.2.2.2.1 rfl cm_bits.2.2.2 e)
      · exact (hsmall m4 hcl.1.1.1 e).elim
      · exact (hsmall m5 hcl.1.1.2 e).elim
      · exact (hsmall m6 hcl.1.2 e).elim
      · exact (hsmall m7 hcl.2 e).elim
    · exact Or.inl (Or.inl (Or.inl (Or.inl hsp)))
  · rw [Bool.not_eq_true] at hpc
    exact Or.inl hpc

end CertificateChecks.Parrott946

end
