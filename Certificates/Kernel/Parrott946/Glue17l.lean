
module

public import Certificates.Kernel.Parrott946.Glue17k

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

theorem mem_NSlist {c : P45} : c ∈ NSlist () ↔ c ∈ HN := by
  rw [NSlist_eq, List.mem_filter, mem_elemsT QA45 QA45_ok, decide_eq_true_eq, normS_iff_all]
  exact (mem_inf).symm

theorem mem_conjOrbit {g x : P45} :
    x ∈ conjOrbit (NSlist ()) g ↔ x ∈ conjClass HN g := by
  unfold conjOrbit
  rw [List.mem_dedup, List.mem_map]
  simp only [tab_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, mem_NSlist.1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, mem_NSlist.2 hc, rfl⟩

theorem orb_parts : (strictB (pidn 45 6) fun e =>
    allL t5R (fun _ rc => orbRec e 13 (wE 0) rc) 0 &&
      allL f5R (fun _ rc => orbRec e 5 (pc (wE 1) (wE 0)) rc) 0) = true := c17_orb.2.2.2.2.1

theorem orbit_ut_sup : invF 5 ⊆ conjClass HN (u * t) := by
  have ho := orb_parts
  rw [strictB_eq', Bool.and_eq_true] at ho
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨c, hc, e⟩ := rec_cover prep_ut ho.2 f5R_k c17_orb.2.2.2.1 c17_orb.2.2.2.2.2.2.2
    card_posF5 j hj
  exact ⟨c, hc, e.symm⟩

theorem t5_pos : ∀ j ∈ [1, 6, 8, 15, 41], j ∈ posF 13 := by
  have ho := orb_parts
  rw [strictB_eq', Bool.and_eq_true] at ho
  have hk := t5R_k
  intro j hj
  have e : [1, 6, 8, 15, 41] = t5R.map fun rc => rc &&& 63 := by decide
  rw [e, List.mem_map] at hj
  obtain ⟨rc, hrc, rfl⟩ := hj
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hrc
  have h := allL_spec ho.1 p hp
  rw [List.getD_eq_getElem _ _ hp] at h
  exact (orbRec_spec prep_t h (hk _ (List.getElem_mem hp))).1

theorem S_eq_t5span {x : P45} : x ∈ Slist () ↔ x ∈ prodSpan ([1, 6, 8, 15, 41].map xI) := by
  rw [mem_S, span_set (mem43 (by decide)) c17_orb.2.2.2.2.2.1 masks_lt.1]

theorem pos_cases {j : ℕ} (hj : j < 43) (hb : bitB D17.M0 j = true) :
    j ∈ posF 13 ∨ j ∈ posF 5 := by
  classical
  let F := (Finset.range 43).filter fun j => bitB D17.M0 j = true
  have hF : F.card = 15 := by rw [← c17_masks.1, cntN_eq]
  have hsub : posF 13 ∪ posF 5 ⊆ F := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    rcases Finset.mem_union.1 hk with hk | hk
    · exact ⟨(mem_posF.1 hk).1, (mem_posF.1 hk).2.1⟩
    · exact ⟨(mem_posF.1 hk).1, (mem_posF.1 hk).2.1⟩
  have hdisj : Disjoint (posF 13) (posF 5) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have := (mem_posF.1 h1).2.2
    rw [(mem_posF.1 h2).2.2] at this
    omega
  have heq : posF 13 ∪ posF 5 = F := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_union_of_disjoint hdisj, card_posF13, card_posF5, hF])
  have hjF : j ∈ F := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hb⟩
  rw [← heq] at hjF
  exact Finset.mem_union.1 hjF

theorem s_orbits : sOrbitCheck (NSlist ()) = true := by
  classical
  have hot : ∀ x, x ∈ conjOrbit (NSlist ()) t ↔ x ∈ invF 13 := fun x => by
    rw [mem_conjOrbit, orbit_t]
  unfold sOrbitCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, tab_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·
    have hnd : (conjOrbit (NSlist ()) t).Nodup := List.nodup_dedup _
    rw [← List.toFinset_card_of_nodup hnd, ← card_posF13]
    have e : (conjOrbit (NSlist ()) t).toFinset = (posF 13).image xI := by
      ext x
      rw [List.mem_toFinset, hot, Finset.mem_image]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    rw [e, Finset.card_image_of_injOn]
    intro j hj k hk ejk
    exact xI_inj (mem_posF.1 hj).1 (mem_posF.1 hk).1 ejk
  ·
    refine List.all_eq_true.2 fun g hg => ?_
    have hgA : g ∈ A := (mem_elemsT QA45 QA45_ok g).1 hg
    rw [Bool.or_eq_true]
    by_cases hc : ∀ o ∈ conjOrbit (NSlist ()) t, g * o = o * g
    · refine Or.inr (decide_eq_true (cent_S hgA fun x hx => ?_))
      have hxS : x ∈ Slist () := (S_set x).2 (subset_closure hx)
      rw [S_eq_t5span] at hxS
      have hmem := prodSpan_mem (centralizer ({g} : Set P45)) (gs := [1, 6, 8, 15, 41].map xI)
        (fun y hy => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
          exact mem_centralizer_singleton_iff.2 (hc _ ((hot _).2 ⟨j, t5_pos j hj, rfl⟩)).symm)
        x hxS
      exact (mem_centralizer_singleton_iff.1 hmem).symm
    · refine Or.inl ?_
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro h
      exact hc fun o ho => of_decide_eq_true (List.all_eq_true.1 h o ho)
  ·
    refine List.all_eq_true.2 fun s hs => ?_
    rw [List.mem_filter, decide_eq_true_eq] at hs
    rw [Bool.or_eq_true]
    rcases mem_S.1 hs.1 with h | ⟨j, hj, hb, rfl⟩
    · exact absurd h hs.2
    · rcases pos_cases hj hb with h | h
      · exact Or.inl (decide_eq_true ((hot _).2 ⟨j, h, rfl⟩))
      · exact Or.inr (decide_eq_true (mem_conjOrbit.2 (orbit_ut_sup ⟨j, h, rfl⟩)))
  ·
    intro h
    obtain ⟨j, hj, e⟩ := (hot _).1 h
    have := (mem_posF.1 hj).2.2
    rw [← e, fixC_ut] at this
    omega

end CertificateChecks.Parrott946

end
