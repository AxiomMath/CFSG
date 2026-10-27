module

public import Certificates.Kernel.HN1408.CbTChk
public import Certificates.Kernel.HN1408.ClsBFacts
public import Certificates.Kernel.HN1408.TabXCntFacts
public import Certificates.Kernel.HN1408.Tab4BlkDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbT

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.KD.HN1408.Tr2 CFSG.KS.BaseEq

theorem cbT_ok : Tr2OK classb.centGens wordB 672 1 nS G T0 P0 S SR T1 P1 where
  letters l hl := by
    have hl2 : l < 2 := hl
    interval_cases l <;> decide
  zw := by decide
  head := cbT_head
  keys := cbT_keys
  tree := cbT_tree
  sch := cbT_sch
  t1 := cbT_t1

theorem t1PK_parts {j : Nat} (h : t1PK 1401 1 nS S T1 P1 j = true) :
    pt (T1 j) 0 = 0 ∧
      (∀ j' < j, pt (T1 j) 1401 = pt (T1 j') 1401 → pt (T1 j) 1 = pt (T1 j') 1 → False) ∧
      (j ≠ 0 → ∃ p r, p < j ∧ r < nS ∧ T1 j = pc (S r) (T1 p)) := by
  unfold t1PK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  refine ⟨Nat.eq_of_beq_eq_true a, fun j' hj' e1 e2 => ?_, fun h0 => ?_⟩
  · have h' := allN_spec b j' hj'
    rw [e1, e2, Nat.beq_refl, Nat.beq_refl] at h'
    exact Bool.false_ne_true h'
  · have e0 : Nat.beq j 0 = false := Bool.eq_false_iff.2 fun h'' => h0 (Nat.eq_of_beq_eq_true h'')
    rw [e0] at h
    simp only [strictB_app] at h
    obtain ⟨c, h⟩ := mkA h
    obtain ⟨d, f⟩ := mkA h
    exact ⟨_, _, Nat.blt_eq.mp c, Nat.blt_eq.mp d, Nat.eq_of_beq_eq_true f⟩

theorem t1Q_mem : ∀ j < 120, ∃ g ∈ genC classb.centGens, RepC (T1 j) g := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h0 : j = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [(headK_parts cbT_ok.head).2.2.2]; exact repC_idK⟩
    · obtain ⟨p, r, hp, hr, e⟩ := (t1PK_parts (allN_spec cbT_t1P j hj)).2.2 h0
      obtain ⟨g, hg, hgR⟩ := ih p hp (by omega)
      obtain ⟨s, hs, hsR⟩ := s_mem cbT_ok hr
      exact ⟨_, mul_mem hs hg, by rw [e]; exact repC_pc hsR hgR⟩

noncomputable def t1Q (j : Nat) : Equiv.Perm (Fin 1408) :=
  if hj : j < 120 then (t1Q_mem j hj).choose else 1

noncomputable def t0Q (i : Nat) : Equiv.Perm (Fin 1408) := t0P cbT_ok i

theorem t0Q_spec {i : Nat} (hi : i < 672) :
    t0Q i ∈ genC classb.centGens ∧ RepC (T0 i) (t0Q i) :=
  t0P_spec cbT_ok hi

theorem t1Q_spec {j : Nat} (hj : j < 120) :
    t1Q j ∈ genC classb.centGens ∧ RepC (T1 j) (t1Q j) := by
  rw [t1Q, dif_pos hj]
  exact (t1Q_mem j hj).choose_spec

theorem t1Q_zero {j : Nat} (hj : j < 120) : t1Q j ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
  Fin.ext (by rw [← repC_pt (t1Q_spec hj).2 (by norm_num), (t1PK_parts (allN_spec cbT_t1P j hj)).1])

theorem t1Q_pt {j x : Nat} (hj : j < 120) (hx : x < 1408) :
    (t1Q j ⟨x, hx⟩).val = pt (T1 j) x :=
  (repC_pt (t1Q_spec hj).2 hx).symm

theorem t1Q_inj {j j' : Nat} (hj : j < 120) (hj' : j' < 120)
    (h1 : t1Q j ⟨1401, by norm_num⟩ = t1Q j' ⟨1401, by norm_num⟩)
    (h2 : t1Q j ⟨1, by norm_num⟩ = t1Q j' ⟨1, by norm_num⟩) : j = j' := by
  have e1 := congrArg Fin.val h1
  have e2 := congrArg Fin.val h2
  rw [t1Q_pt hj, t1Q_pt hj'] at e1 e2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (t1PK_parts (allN_spec cbT_t1P j' hj')).2.1 j hlt e1.symm e2.symm
  · exact (t1PK_parts (allN_spec cbT_t1P j hj)).2.1 j' hlt e1 e2

theorem el_inj {i i' j j' : Nat} (hi : i < 672) (hi' : i' < 672) (hj : j < 120) (hj' : j' < 120)
    (he : t0Q i * t1Q j = t0Q i' * t1Q j') : i = i' ∧ j = j' := by
  have h0 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨0, by norm_num⟩) he
  simp only [Equiv.Perm.mul_apply, t1Q_zero hj, t1Q_zero hj'] at h0
  have ei := t0P_inj cbT_ok hi hi' h0
  subst ei
  have h1 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨1401, by norm_num⟩) he
  have h2 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨1, by norm_num⟩) he
  simp only [Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq] at h1 h2
  exact ⟨rfl, t1Q_inj hj hj' h1 h2⟩

theorem ev_eq {i j x : Nat} (hi : i < 672) (hj : j < 120) (hx : x < 1408) :
    pt (T0 i) (pt (T1 j) x) = ((t0Q i * t1Q j) ⟨x, hx⟩).val := by
  rw [← pt_pc (t0Q_spec hi).2.1 hx]
  exact repC_pt (repC_pc (t0Q_spec hi).2 (t1Q_spec hj).2) hx

theorem mem_iff (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)} :
    g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ↔
      ∃ i < 672, ∃ j < 120, g = t0Q i * t1Q j := by
  classical
  have hcard : Nat.card ↥(P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408)))) =
      80640 := (ClsR.b_facts hP).2.1
  have hle := le_cent cbT_ok
  let E : Finset (Equiv.Perm (Fin 1408)) :=
    (Finset.range 672 ×ˢ Finset.range 120).image fun p => t0Q p.1 * t1Q p.2
  have hinj : Set.InjOn (fun p : Nat × Nat => t0Q p.1 * t1Q p.2)
      ↑(Finset.range 672 ×ˢ Finset.range 120) := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' e
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hp'
    obtain ⟨h1, h2⟩ := el_inj hp.1 hp'.1 hp.2 hp'.2 e
    rw [h1, h2]
  have hE : E.card = 80640 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
      Finset.card_range]
  have hsub : (↑E : Set (Equiv.Perm (Fin 1408))) ⊆
      ((P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) :
        Subgroup (Equiv.Perm (Fin 1408))) : Set (Equiv.Perm (Fin 1408))) := by
    intro x hx
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact hle (mul_mem (t0Q_spec hp.1).1 (t1Q_spec hp.2).1)
  have hc : ((P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) :
      Subgroup (Equiv.Perm (Fin 1408))) : Set (Equiv.Perm (Fin 1408))).ncard = 80640 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq : (↑E : Set (Equiv.Perm (Fin 1408))) =
      ((P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) :
        Subgroup (Equiv.Perm (Fin 1408))) : Set (Equiv.Perm (Fin 1408))) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc, Set.ncard_coe_finset, hE]) (Set.toFinite _)
  constructor
  · intro hg
    have hg' : g ∈ (↑E : Set (Equiv.Perm (Fin 1408))) := by
      rw [heq]
      exact hg
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.1 hg'
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact ⟨i, hp.1, j, hp.2, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact hle (mul_mem (t0Q_spec hi).1 (t1Q_spec hj).1)

@[expose] noncomputable def cbSet (F : Nat → Nat → Bool) (n : Nat) : Finset (Nat × Nat) :=
  (Finset.range n ×ˢ Finset.range 120).filter fun p => F (T0 p.1) (T1 p.2) = true

theorem cbSet_succ (F : Nat → Nat → Bool) (n : Nat) :
    (cbSet F (n + 1)).card =
      (cbSet F n).card + ((Finset.range 120).filter fun j => F (T0 n) (T1 j) = true).card := by
  have hinj : Function.Injective fun j : Nat => (n, j) := fun a b h => (Prod.mk.inj h).2
  have hd : Disjoint (cbSet F n)
      (((Finset.range 120).filter fun j => F (T0 n) (T1 j) = true).image fun j => (n, j)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [cbSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    exact lt_irrefl _ hp.1.1
  have he : cbSet F (n + 1) = cbSet F n ∪
      (((Finset.range 120).filter fun j => F (T0 n) (T1 j) = true).image fun j => (n, j)) := by
    ext ⟨i, j⟩
    rw [Finset.mem_union, Finset.mem_image]
    simp only [cbSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hi, hj⟩, hF⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact Or.inl ⟨⟨hi, hj⟩, hF⟩
      · subst hi
        exact Or.inr ⟨j, ⟨hj, hF⟩, rfl, rfl⟩
    · rintro (⟨⟨hi, hj⟩, hF⟩ | ⟨j', ⟨hj, hF⟩, hn, hj'⟩)
      · exact ⟨⟨by omega, hj⟩, hF⟩
      · subst hn hj'
        exact ⟨⟨by omega, hj⟩, hF⟩
  rw [he, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hinj]

theorem cnt2_rec (F : Nat → Nat → Bool) :
    ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i ih => strictN ih fun a =>
        Nat.add a (strictN (T0 i) fun A => cntN 120 fun j => F A (T1 j))) n =
        (cbSet F n).card
  | 0 => rfl
  | n + 1 => by
    change strictN _ (fun a => Nat.add a (strictN (T0 n) fun A => cntN 120 fun j => F A (T1 j))) = _
    rw [TabX.strictN_eq', TabX.strictN_eq', cnt2_rec F n, cbSet_succ, TabX.cntN_eq']
    rfl

theorem cnt2_eq (F : Nat → Nat → Bool) : cnt2 672 120 T0 T1 F = (cbSet F 672).card :=
  cnt2_rec F 672

theorem ncard_eq_cnt2 (hP : Nat.card ↥P1408 = 177408000) {F : Nat → Nat → Bool}
    {Q : Equiv.Perm (Fin 1408) → Prop}
    (hQ : ∀ i < 672, ∀ j < 120, (F (T0 i) (T1 j) = true ↔ Q (t0Q i * t1Q j))) :
    {g | g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ∧ Q g}.ncard =
      cnt2 672 120 T0 T1 F := by
  classical
  rw [cnt2_eq]
  have hinj : Set.InjOn (fun p : Nat × Nat => t0Q p.1 * t1Q p.2) ↑(cbSet F 672) := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' e
    simp only [cbSet, Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
      at hp hp'
    obtain ⟨h1, h2⟩ := el_inj hp.1.1 hp'.1.1 hp.1.2 hp'.1.2 e
    rw [h1, h2]
  have himg : {g | g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ∧ Q g} =
      ↑((cbSet F 672).image fun p => t0Q p.1 * t1Q p.2) := by
    ext g
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, cbSet, Finset.coe_filter,
      Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨hg, hq⟩
      obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
      exact ⟨i, j, ⟨⟨hi, hj⟩, (hQ i hi j hj).2 hq⟩, rfl⟩
    · rintro ⟨i, j, ⟨⟨hi, hj⟩, hF⟩, rfl⟩
      exact ⟨(mem_iff hP).2 ⟨i, hi, j, hj, rfl⟩, (hQ i hi j hj).1 hF⟩
  rw [himg, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

theorem scan2_spec {F : Nat → Nat → Bool} (h : scan2 F = true) :
    ∀ i < 672, ∀ j < 120, F (T0 i) (T1 j) = true := by
  intro i hi j hj
  unfold scan2 at h
  have h1 := allN_spec h i hi
  rw [strictB_app] at h1
  exact allN_spec h1 j hj

theorem forall_of_scan2 (hP : Nat.card ↥P1408 = 177408000) {F : Nat → Nat → Bool}
    {Q : Equiv.Perm (Fin 1408) → Prop} (h : scan2 F = true)
    (hQ : ∀ i < 672, ∀ j < 120, F (T0 i) (T1 j) = true → Q (t0Q i * t1Q j)) :
    ∀ g ∈ P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))), Q g := by
  intro g hg
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
  exact hQ i hi j hj (scan2_spec h i hi j hj)

end CFSG.KD.HN1408.CbT

end
