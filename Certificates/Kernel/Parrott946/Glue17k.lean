
module

public import Certificates.Kernel.Parrott946.Glue17j

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.SmallOddCore

local notation "P45" => Equiv.Perm (Fin 45)

abbrev HN : Subgroup P45 := A ⊓ NS

@[expose] noncomputable def posF (f : ℕ) : Finset ℕ :=
  (Finset.range 43).filter fun j => (bitB D17.M0 j && Nat.beq (fixK 45 6 (iE j)) f) = true

theorem mem_posF {f j : ℕ} : j ∈ posF f ↔ j < 43 ∧ bitB D17.M0 j = true ∧ fixC (xI j) = f := by
  unfold posF
  rw [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, Nat.beq_eq]
  constructor
  · rintro ⟨hj, hb, hf⟩
    exact ⟨hj, hb, by rw [← fixK_eq (xI_spec hj).1]; exact hf⟩
  · rintro ⟨hj, hb, hf⟩
    exact ⟨hj, hb, by rw [fixK_eq (xI_spec hj).1]; exact hf⟩

theorem card_posF13 : (posF 13).card = 5 := by rw [← c17_orb.1, cntN_eq]; rfl

theorem card_posF5 : (posF 5).card = 10 := by rw [← c17_orb.2.1, cntN_eq]; rfl

theorem orbRec_spec {f : ℕ} {Z rc : ℕ} {z : P45} (hz : PRep 45 6 Z z)
    (h : orbRec (pidn 45 6) f Z rc = true) (hk : rc >>> 6 < 49) :
    (rc &&& 63) ∈ posF f ∧ wv17 (rc >>> 6) ∈ HN ∧
      wv17 (rc >>> 6) * z * (wv17 (rc >>> 6))⁻¹ = xI (rc &&& 63) := by
  unfold orbRec at h
  rw [strictB_eq', strictB_eq'] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hb, hf⟩, he⟩, hn⟩ := h
  have hj : rc &&& 63 < 43 := by
    by_contra hj
    rw [not_lt] at hj
    have hf' : D17.M0.testBit (Nat.land rc 63) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le masks_lt.1 (Nat.pow_le_pow_right (by norm_num) hj))
    rw [(bitB_iff _ _).1 hb] at hf'
    exact absurd hf' (by decide)
  have hw := prep_wE hk
  refine ⟨mem_posF.2 ⟨hj, hb, ?_⟩, mem_inf.2 ⟨hw.2, mem_normalizer_of (normS_of_mask hw.1 hn)⟩, ?_⟩
  · rw [← fixK_eq (xI_spec hj).1]
    exact Nat.eq_of_beq_eq_true hf
  · have e := mul_eq_of_eq22 hw.1 hz (xI_spec hj).1 hw.1 he
    rw [e, mul_inv_cancel_right]

theorem t5R_k : ∀ rc ∈ t5R, rc >>> 6 < 49 := by decide
theorem f5R_k : ∀ rc ∈ f5R, rc >>> 6 < 49 := by decide

theorem rec_cover {f n : ℕ} {l : List ℕ} {Z : ℕ} {z : P45} (hz : PRep 45 6 Z z)
    (hall : allL l (fun _ rc => orbRec (pidn 45 6) f Z rc) 0 = true)
    (hk : ∀ rc ∈ l, rc >>> 6 < 49)
    (hchain : ltChainK (mapK (fun rc => Nat.succ (Nat.land rc 63)) l) 0 = true)
    (hlen : lenK l = n) (hcard : (posF f).card = n) :
    ∀ j ∈ posF f, ∃ c ∈ HN, c * z * c⁻¹ = xI j := by
  classical
  have hspec : ∀ rc ∈ l, (rc &&& 63) ∈ posF f ∧ wv17 (rc >>> 6) ∈ HN ∧
      wv17 (rc >>> 6) * z * (wv17 (rc >>> 6))⁻¹ = xI (rc &&& 63) := by
    intro rc hrc
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hrc
    have := allL_spec hall j hj
    rw [List.getD_eq_getElem _ _ hj] at this
    exact orbRec_spec hz this (hk _ hrc)
  have hp := (ltChainK_spec hchain).1
  rw [mapK_eq, List.pairwise_map] at hp
  have hq : (l.map fun rc => rc &&& 63).Pairwise (· < ·) :=
    List.pairwise_map.2 (hp.imp fun h => Nat.succ_lt_succ_iff.1 h)
  have hnd : (l.map fun rc => rc &&& 63).Nodup := hq.imp ne_of_lt
  have hsub : (l.map fun rc => rc &&& 63).toFinset ⊆ posF f := by
    intro j hj
    rw [List.mem_toFinset, List.mem_map] at hj
    obtain ⟨rc, hrc, rfl⟩ := hj
    exact (hspec rc hrc).1
  have heq : (l.map fun rc => rc &&& 63).toFinset = posF f :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hnd, List.length_map, ← lenK_eq, hlen, hcard])
  intro j hj
  rw [← heq, List.mem_toFinset, List.mem_map] at hj
  obtain ⟨rc, hrc, rfl⟩ := hj
  exact ⟨_, (hspec rc hrc).2.1, (hspec rc hrc).2.2⟩

@[expose] def invF (f : ℕ) : Set P45 := {x | ∃ j ∈ posF f, x = xI j}

theorem ncard_invF (f : ℕ) : (invF f).ncard = (posF f).card := by
  have e : invF f = ((posF f).image xI : Set P45) := by
    ext x
    simp only [invF, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  rw [e, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  intro j hj k hk ejk
  exact xI_inj (mem_posF.1 hj).1 (mem_posF.1 hk).1 ejk

theorem conj_mem_S {c x : P45} (hc : c ∈ HN) (hx : x ∈ Slist ()) : c * x * c⁻¹ ∈ Slist () :=
  (S_set _).2 ((mem_normalizer_iff.1 (mem_inf.1 hc).2 x).1 ((S_set x).1 hx))

theorem t_mem_S : t ∈ Slist () := (S_set t).2 (subset_closure t_mem_Sgens)

theorem orbit_t : conjClass HN t = invF 13 := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases mem_S.1 (conj_mem_S hc t_mem_S) with h | ⟨j, hj, hb, e⟩
    · exfalso
      apply Alg.t_ne_one
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · refine ⟨j, mem_posF.2 ⟨hj, hb, ?_⟩, e⟩
      rw [← e, fixC_conj, fixC_t]
  · rintro ⟨j, hj, rfl⟩
    have ho := c17_orb.2.2.2.2.1
    rw [strictB_eq', Bool.and_eq_true] at ho
    obtain ⟨c, hc, e⟩ := rec_cover prep_t ho.1 t5R_k c17_orb.2.2.1 c17_orb.2.2.2.2.2.2.1
      card_posF13 j hj
    exact ⟨c, hc, e.symm⟩

theorem rr_norm {i : ℕ} (hi : i = 0 ∨ i = 5 ∨ i = 6) : rr i ∈ NS := by
  have h := c17_ns
  rw [strictB_eq'] at h
  simp only [Bool.and_eq_true] at h
  rcases hi with rfl | rfl | rfl
  · rw [rr_zero]
    exact NS.one_mem
  · exact mem_normalizer_of (normS_of_mask (prep_rr (by norm_num)).1 h.1.1.1.1.1.1.2)
  · exact mem_normalizer_of (normS_of_mask (prep_rr (by norm_num)).1 h.1.1.1.1.1.2)

@[expose] def i3 (p : Fin 3) : ℕ := [0, 5, 6].getD p 0

theorem i3_spec (p : Fin 3) : i3 p < 9 ∧ (i3 p = 0 ∨ i3 p = 5 ∨ i3 p = 6) := by
  fin_cases p <;> simp [i3]

theorem i3_inj {p q : Fin 3} (h : i3 p = i3 q) : p = q := by
  fin_cases p <;> fin_cases q <;> simp_all [i3]

theorem card_Ht :
    Nat.card ↥(HN ⊓ centralizer ({t} : Set P45)) = 384 := by
  have hmem : ∀ p : Fin 3, ∀ s ∈ T0g, s * rr (i3 p) ∈ HN ⊓ centralizer ({t} : Set P45) := by
    intro p s hs
    have hi := i3_spec p
    have hs' := T0g_le_cent hs
    refine mem_inf.2 ⟨mem_inf.2 ⟨A.mul_mem (mem_inf.1 hs').1 (prep_rr hi.1).2,
      NS.mul_mem (T0g_le_norm hs) (rr_norm hi.2)⟩, ?_⟩
    exact (centralizer ({t} : Set P45)).mul_mem (mem_inf.1 hs').2
      (mem_centralizer_singleton_iff.2 (cos_facts hi.1).2)
  let f : Fin 3 × T0g → ↥(HN ⊓ centralizer ({t} : Set P45)) := fun p =>
    ⟨p.2.1 * rr (i3 p.1), hmem p.1 p.2.1 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨p, s⟩ ⟨q, s'⟩ e
    have e' : s.1 * rr (i3 p) = s'.1 * rr (i3 q) := congrArg Subtype.val e
    have key : ∀ {a b : ℕ} {x y : P45}, a < 9 → b < 9 → x ∈ T0g → y ∈ T0g → a < b →
        x * rr a = y * rr b → False := by
      intro a b x y ha hb hx hy hab e2
      apply cos_sep ha hb hab
      have : rr b * (rr a)⁻¹ = y⁻¹ * x := by
        calc rr b * (rr a)⁻¹ = y⁻¹ * (y * rr b) * (rr a)⁻¹ := by group
          _ = y⁻¹ * (x * rr a) * (rr a)⁻¹ := by rw [e2]
          _ = y⁻¹ * x := by group
      rw [this]
      exact T0g.mul_mem (T0g.inv_mem hy) hx
    rcases lt_trichotomy (i3 p) (i3 q) with h | h | h
    · exact (key (i3_spec p).1 (i3_spec q).1 s.2 s'.2 h e').elim
    · have hpq : p = q := i3_inj h
      subst hpq
      have : s.1 = s'.1 := mul_right_cancel e'
      rw [Subtype.ext this]
    · exact (key (i3_spec q).1 (i3_spec p).1 s'.2 s.2 h e'.symm).elim
  have hsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    have hc1 := mem_inf.1 hc
    have hcA := (mem_inf.1 hc1.1).1
    have hcN := (mem_inf.1 hc1.1).2
    obtain ⟨i, hi, hs⟩ := cent_t_cosets hcA (mem_centralizer_singleton_iff.1 hc1.2)
    have hrN : NormS (rr i) := by
      refine normS_of_mem ?_
      have e : rr i = (c * (rr i)⁻¹)⁻¹ * c := by group
      rw [e]
      exact NS.mul_mem (NS.inv_mem (T0g_le_norm hs)) hcN
    have hp : ∃ p : Fin 3, i3 p = i := by
      rcases rep_norm hi hrN with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨p, rfl⟩ := hp
    refine ⟨⟨p, ⟨c * (rr (i3 p))⁻¹, hs⟩⟩, Subtype.ext ?_⟩
    change c * (rr (i3 p))⁻¹ * rr (i3 p) = c
    group
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_fin, card_T0g]

theorem card_NS : Nat.card HN = 1920 := by
  have h := ncard_conjClass_mul_card HN t
  rw [orbit_t, ncard_invF, card_posF13, card_Ht] at h
  omega

theorem NSlist_eq : NSlist () = (elemsT QA45).filter fun g =>
    decide ((Sgens.all fun x => decide (g * x * g⁻¹ ∈ Slist ())) = true) := by
  simp only [NSlist, tabList_eq, Bool.decide_eq_true]

theorem normS_iff_all {g : P45} :
    (Sgens.all fun x => decide (g * x * g⁻¹ ∈ Slist ())) = true ↔ g ∈ NS := by
  rw [List.all_eq_true]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => mem_normalizer_of h, fun h => normS_of_mem h⟩

theorem s_normalizer_card : (NSlist ()).length = 1920 := by
  rw [NSlist_eq, ← card_filter QA45 QA45_ok
    (p := fun g => (Sgens.all fun x => decide (g * x * g⁻¹ ∈ Slist ())) = true), ← card_NS]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.1.1, mem_inf.2 ⟨g.1.2, normS_iff_all.1 g.2⟩⟩
      invFun := fun g => ⟨⟨g.1, (mem_inf.1 g.2).1⟩, normS_iff_all.2 (mem_inf.1 g.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CertificateChecks.Parrott946

end
