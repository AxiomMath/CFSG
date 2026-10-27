
module

public import Certificates.Kernel.J4Count.FixZBase1

public import CFSG.Certificates.Kernel.J4CountSound
public import CFSG.Sporadic.J4.Struct.FixCount
public import CFSG.Quasithin.H13.J4CentralizerBase1
public import Certificates.Kernel.J4Count.HOrder

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.KC.J4Count CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4NoCP

section Rep

theorem fix_iff_etaV {l : ℕ} (hl : l < 7) {a : ℕ} (ha : a < 2048) :
    η a • qv l = qv l ↔ etaV unMats repVecs[l]! a = repVecs[l]! := by
  rw [η_smul_toRow]
  constructor
  · intro h
    exact toVecD_injOn (congrArg ofRow h) (((fix_check l hl).2 a ha))
  · intro h
    rw [h]

theorem fix_iff_combo {l : ℕ} (hl : l < 7) {a : ℕ} (ha : a < 2048) :
    η a • qv l = qv l ↔ combo (getL BS l) (decode (getL PS l) a) = a := by
  classical
  obtain ⟨hlen, hsize, hB, hinv⟩ := basis_parts hl
  set B := getL BS l
  set P := getL PS l
  have hT : ∀ m, combo B m < 2048 ∧ η (combo B m) • qv l = qv l := by
    refine combo_mem (S := fun a => a < 2048 ∧ η a • qv l = qv l) ⟨by norm_num, by
      rw [η_zero, one_smul]⟩ (fun a b ha hb => ⟨?_, ?_⟩) (fun b hb => ⟨(hB b hb).1, ?_⟩)
    · exact Nat.xor_lt_two_pow (n := 11) ha.1 hb.1
    · rw [η_xor, mul_smul, hb.2, ha.2]
    · rw [fix_iff_etaV hl (hB b hb).1, J4NoCP.etaV_eq, rv_get hl]
      exact (hB b hb).2
  set S := (Finset.range 2048).filter fun a => η a • qv l = qv l
  have hS : S.card = repCounts[l]! := by
    rw [← (fix_check l hl).1]
    congr 1
    exact Finset.filter_congr fun a ha => fix_iff_etaV hl (Finset.mem_range.1 ha)
  have hsub : (Finset.range (2 ^ B.length)).image (combo B) ⊆ S := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hT m).1, (hT m).2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hS, card_image hinv, hsize])
  rw [← mem_image_iff hlen hinv a]
  constructor
  · intro h
    have : a ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, h⟩
    rw [← heq] at this
    obtain ⟨m, hm, e⟩ := Finset.mem_image.1 this
    exact ⟨m, Finset.mem_range.1 hm, e⟩
  · rintro ⟨m, -, rfl⟩
    exact (hT m).2

theorem card_fix_rep {l : ℕ} (hl : l < 7) :
    ((Finset.range 1771).filter fun i => etaV unMats repVecs[l]! orb1.1[i]! = repVecs[l]!).card =
      CZ.getD l 0 := by
  have h := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec cnt_ok l hl)
  unfold cntZ at h
  rw [cntK_eq] at h
  have e : CFSG.KC.J4Q.getN 0 CZ l = CZ.getD l 0 := by interval_cases l <;> rfl
  rw [← e, ← h]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hlt : orb1.1[i]! < 2048 := bfsOK_lt orb1_ok hi'
  rw [← fix_iff_etaV hl hlt, fix_iff_combo hl hlt, orb1_pt hi', Nat.beq_eq]

end Rep

section Class

theorem isConj_zH_iff (s : H) : IsConj zH s ↔ ∃ i < 1771, (s : J) = η orb1.1[i]! := by
  have e : ∀ m : J, m ∈ CFSG.Sporadic.J4Schreier.conjOrbit H z ↔ ∃ i < 1771, m = η orb1.1[i]! := by
    intro m
    rw [conjOrbit_H_z', ← CFSG.Quasithin.H13.J4Classes.η_one,
      conjOrbit_one]
    rfl
  rw [← e, isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.1, c.2, rfl⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨⟨k, hk⟩, Subtype.ext he.symm⟩

theorem card_class_zH : Nat.card {s : H // IsConj zH s} = 1771 := by
  rw [← ncard_class_e1', ← Nat.card_coe_set_eq]
  refine Nat.card_congr
    { toFun := fun s => ⟨s.1.1, ?_⟩
      invFun := fun m => ⟨⟨m.1, ?_⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · obtain ⟨c, hc⟩ := isConj_iff.1 s.2
    exact ⟨c.1, c.2, by rw [← hc]; rfl⟩
  · obtain ⟨k, hk, he⟩ := m.2
    rw [he]
    exact H.mul_mem (H.mul_mem hk z_mem_H) (H.inv_mem hk)
  · obtain ⟨k, hk, he⟩ := m.2
    exact isConj_iff.2 ⟨⟨k, hk⟩, Subtype.ext he.symm⟩

theorem mem_fixRecs {l : ℕ} (hl : l < 7) {i : ℕ} :
    i ∈ fixRecs l ↔ i < 1771 ∧ η orb1.1[i]! • qv l = qv l := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨hi, (fix_iff_etaV hl (bfsOK_lt orb1_ok hi)).2 h⟩
  · rintro ⟨hi, h⟩
    exact ⟨hi, (fix_iff_etaV hl (bfsOK_lt orb1_ok hi)).1 h⟩

theorem card_stab_class {l : ℕ} (hl : l < 7) :
    Nat.card {s : H // s ∈ stabilizer H (qv l) ∧ IsConj zH s} = CZ.getD l 0 := by
  rw [← card_fix_rep hl]
  change _ = (fixRecs l).card
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  symm
  have hS : ∀ i ∈ fixRecs l, recElt i ∈ stabilizer H (qv l) ∧ IsConj zH (recElt i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := (mem_fixRecs hl).1 hi
    refine ⟨(mem_stab_iff _ _).2 (by rw [recElt_val]; exact hi2), (isConj_zH_iff _).2 ⟨i, hi1, ?_⟩⟩
    rw [recElt_val]
  let f : {i // i ∈ fixRecs l} → {s : H // s ∈ stabilizer H (qv l) ∧ IsConj zH s} :=
    fun i => ⟨recElt i.1, hS i.1 i.2⟩
  have hf : ∀ i, (f i : H) = recElt i.1 := fun _ => rfl
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun i k e => ?_, fun s => ?_⟩)
  · have hi' := ((mem_fixRecs hl).1 i.2).1
    have hk' := ((mem_fixRecs hl).1 k.2).1
    have e1 := congrArg
      (fun s : {s : H // s ∈ stabilizer H (qv l) ∧ IsConj zH s} => ((s.1 : H) : J)) e
    simp only [hf, recElt_val] at e1
    have := η_injOn (bfsOK_lt orb1_ok hi') (bfsOK_lt orb1_ok hk') e1
    by_contra hne
    exact bfsOK_ne orb1_ok hi' hk' (fun h => hne (Subtype.ext h)) this
  · obtain ⟨s, hs, hc⟩ := s
    obtain ⟨i, hi, he⟩ := (isConj_zH_iff s).1 hc
    have hfix : η orb1.1[i]! • qv l = qv l := by
      rw [← he]
      exact (mem_stab_iff _ _).1 hs
    refine ⟨⟨i, (mem_fixRecs hl).2 ⟨hi, hfix⟩⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hf, recElt_val, he]

theorem finite_H : Finite H :=
  Nat.finite_of_card_ne_zero (by rw [card_H']; norm_num)

theorem card_fix_z_suborbit {l : ℕ} (hl : l < 7) :
    Nat.card {x : Row // x ∈ orbit H (qv l) ∧ z • x = x} * 1771 =
      (orbit H (qv l)).ncard * CZ.getD l 0 := by
  have := finite_H
  have h := CFSG.Sporadic.J4.Struct.card_fix_orbit_mul_card_conj (G := H) (X := Row) (qv l) zH
  rw [card_class_zH, card_stab_class hl] at h
  exact h

end Class

theorem card_fix_z_of (hcov : ∀ w ∈ orbit J v, ∃ l < 7, w ∈ orbit H (qv l))
    (hsz : ∀ l < 7, (orbit H (qv l)).ncard = SZ.getD l 0) :
    Nat.card {w : Row // w ∈ orbit J v ∧ z • w = w} = 52349 := by
  classical
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have hfinO : (orbit J v).Finite := Set.finite_range _
  set F : Set Row := {w | w ∈ orbit J v ∧ z • w = w}
  set Fl : ℕ → Set Row := fun l => {w | w ∈ orbit H (qv l) ∧ z • w = w}
  have hFl_sub : ∀ l < 7, Fl l ⊆ F := fun l hl w hw => ⟨orbit_H_subset hl hw.1, hw.2⟩
  have hfinF : F.Finite := hfinO.subset fun w hw => hw.1
  have hfinFl : ∀ l < 7, (Fl l).Finite := fun l hl => hfinF.subset (hFl_sub l hl)
  have hU : hfinF.toFinset = (Finset.range 7).biUnion fun l =>
      if hl : l < 7 then (hfinFl l hl).toFinset else ∅ := by
    ext w
    simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro hw
      obtain ⟨l, hl, hwl⟩ := hcov w hw.1
      exact ⟨l, hl, by rw [dif_pos hl, Set.Finite.mem_toFinset]; exact ⟨hwl, hw.2⟩⟩
    · rintro ⟨l, hl, hw⟩
      rw [dif_pos hl, Set.Finite.mem_toFinset] at hw
      exact hFl_sub l hl hw
  have hdisj : (↑(Finset.range 7) : Set ℕ).PairwiseDisjoint fun l =>
      if hl : l < 7 then (hfinFl l hl).toFinset else ∅ := by
    intro l hl l' hl' hne
    have hl7 : l < 7 := Finset.mem_range.1 hl
    have hl7' : l' < 7 := Finset.mem_range.1 hl'
    simp only [Function.onFun, dif_pos hl7, dif_pos hl7']
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [Set.Finite.mem_toFinset] at hw hw'
    have e1 : orbit H (qv l) = orbit H w := (orbit_eq_iff.2 hw.1).symm
    have e2 : orbit H (qv l') = orbit H w := (orbit_eq_iff.2 hw'.1).symm
    have e : SZ.getD l 0 = SZ.getD l' 0 := by rw [← hsz l hl7, ← hsz l' hl7', e1, e2]
    exact hne (SZ_inj l hl7 l' hl7' e)
  have hcard : ∀ l (hl : l < 7), (hfinFl l hl).toFinset.card * 1771 =
      SZ.getD l 0 * CZ.getD l 0 := by
    intro l hl
    rw [← hsz l hl, ← card_fix_z_suborbit hl, ← Set.ncard_eq_toFinset_card _ (hfinFl l hl),
      ← Nat.card_coe_set_eq]
    rfl
  rw [show Nat.card {w : Row // w ∈ orbit J v ∧ z • w = w} = hfinF.toFinset.card by
    rw [← Set.ncard_eq_toFinset_card _ hfinF, ← Nat.card_coe_set_eq]; rfl, hU,
    Finset.card_biUnion hdisj]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  have c0 := hcard 0 (by norm_num)
  have c1 := hcard 1 (by norm_num)
  have c2 := hcard 2 (by norm_num)
  have c3 := hcard 3 (by norm_num)
  have c4 := hcard 4 (by norm_num)
  have c5 := hcard 5 (by norm_num)
  have c6 := hcard 6 (by norm_num)
  simp only [SZ, CZ, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2 c3 c4 c5 c6
  simp only [show (0 : ℕ) < 7 by norm_num, show (1 : ℕ) < 7 by norm_num,
    show (2 : ℕ) < 7 by norm_num, show (3 : ℕ) < 7 by norm_num, show (4 : ℕ) < 7 by norm_num,
    show (5 : ℕ) < 7 by norm_num, show (6 : ℕ) < 7 by norm_num, dif_pos]
  omega

theorem card_fix_tJ_of
    (hcov : ∀ w ∈ orbit J v, ∃ l < 7, w ∈ orbit H (qv l))
    (hsz : ∀ l < 7, (orbit H (qv l)).ncard = SZ.getD l 0) :
    Nat.card {w : Row // w ∈ orbit J v ∧ CFSG.Quasithin.H13.J4.tJ • w = w} = 52349 := by
  rw [CFSG.Sporadic.J4.Struct.card_fix_conj (orbit J v)
    (fun g x hx => by obtain ⟨k, rfl⟩ := hx; exact ⟨g * k, mul_smul g k v⟩)
    CFSG.Quasithin.H13.J4.isConj_tJ_e1]
  exact card_fix_z_of hcov hsz

end CertificateChecks.KernelJ4Count

end
