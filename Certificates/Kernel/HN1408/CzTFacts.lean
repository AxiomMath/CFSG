
module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.CzTChk
public import Certificates.Kernel.HN1408.CzTTree
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzT

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

#kc_forall_chunks tree_all (fun s => treeSl s = true) 20 CFSG.KD.HN1408.chCzT.tree 1

abbrev czC : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ classz.centGens})

theorem repC_idK : RepC idK 1 := ⟨cId, by rw [← idT_eq]; exact Rep.idT (by norm_num)⟩

theorem repC_of_pt {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (h : ∀ x (hx : x < 1408), pt X x = (g ⟨x, hx⟩).val) : RepC X g :=
  ⟨hX, fun x hx => by rw [ap_eq hX hx, h x hx, idx_of_lt g hx, Equiv.Perm.smul_def]⟩

theorem fd_lt (W i : Nat) : fd W i < 65536 := by
  unfold fd
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem gen_word {l : Nat} (hl : l < 2) : classz.centGens.getD l [] ∈ classz.centGens := by
  interval_cases l <;> decide

theorem gen_letters {l : Nat} (hl : l < 2) : lettersOK (classz.centGens.getD l []) = true := by
  interval_cases l <;> decide

theorem gen_mem {l : Nat} (hl : l < 2) : elemW (classz.centGens.getD l []) ∈ czC :=
  subset_closure ⟨_, gen_word hl, rfl⟩

theorem headK_parts {G T0 T1 : Nat → Nat} (h : headK G T0 T1 = true) :
    (∀ l < 2, G l = WK (classz.centGens.getD l [])) ∧ (∀ l < 2, commP (G l) (WK wordZ) = true) ∧
      T0 0 = idK ∧ T1 0 = idK := by
  unfold headK at h
  generalize WK wordZ = Z at h ⊢
  obtain ⟨h1, h⟩ := mkA h
  obtain ⟨h2, h⟩ := mkA h
  obtain ⟨h3, h4⟩ := mkA h
  rw [strictB_app] at h2
  exact ⟨fun l hl => Nat.eq_of_beq_eq_true (allN_spec h1 l hl), fun l hl => allN_spec h2 l hl,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem head_parts :
    (∀ l < 2, G l = WK (classz.centGens.getD l [])) ∧ (∀ l < 2, commP (G l) (WK wordZ) = true) ∧
      T0 0 = idK ∧ T1 0 = idK :=
  headK_parts czT_head

theorem repC_G {l : Nat} (hl : l < 2) : RepC (G l) (elemW (classz.centGens.getD l [])) := by
  rw [head_parts.1 l hl]
  exact repC_word (gen_letters hl)

theorem treeK_parts {G T0 P0 : Nat → Nat} {i : Nat} (h : treeK G T0 P0 i = true) (h0 : i ≠ 0) :
    ∃ p l, p < 1280 ∧ l < 2 ∧ fd (P0 i) 2 = fd (P0 p) 2 + 1 ∧ T0 i = pc (G l) (T0 p) := by
  unfold treeK at h
  have e0 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h'' => h0 (Nat.eq_of_beq_eq_true h'')
  rw [e0] at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨_, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d⟩

theorem tree_parts {i : Nat} (hi : i < 1280) (h0 : i ≠ 0) :
    ∃ p l, p < 1280 ∧ l < 2 ∧ fd (P0 i) 2 = fd (P0 p) 2 + 1 ∧ T0 i = pc (G l) (T0 p) := by
  have hs : i / 64 < 20 := by omega
  have h := tree_all (i / 64) hs
  unfold treeSl at h
  have h' := allN_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h'
  exact treeK_parts h' h0

theorem t0_mem : ∀ i < 1280, ∃ g ∈ czC, RepC (T0 i) g := by
  suffices H : ∀ d i, fd (P0 i) 2 = d → i < 1280 → ∃ g ∈ czC, RepC (T0 i) g from
    fun i hi => H _ i rfl hi
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hd hi
    by_cases h0 : i = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [head_parts.2.2.1]; exact repC_idK⟩
    · obtain ⟨p, l, hp, hl, hdp, e⟩ := tree_parts hi h0
      obtain ⟨g, hg, hgR⟩ := ih _ (by omega) p rfl hp
      exact ⟨_, mul_mem (gen_mem hl) hg, by rw [e]; exact repC_pc (repC_G hl) hgR⟩

theorem schK_parts {G T0 S SR : Nat → Nat} {r : Nat} (h : schK G T0 S SR r = true) :
    ∃ p q l, p < 1280 ∧ q < 1280 ∧ l < 2 ∧ Cn (S r) ∧ pc (T0 q) (S r) = pc (G l) (T0 p) := by
  unfold schK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  exact ⟨_, _, _, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.blt_eq.mp d, a, Nat.eq_of_beq_eq_true f⟩

theorem sch_parts {r : Nat} (hr : r < nS) :
    ∃ p q l, p < 1280 ∧ q < 1280 ∧ l < 2 ∧ Cn (S r) ∧ pc (T0 q) (S r) = pc (G l) (T0 p) :=
  schK_parts (allN_spec czT_sch r hr)

theorem s_mem {r : Nat} (hr : r < nS) : ∃ g ∈ czC, RepC (S r) g := by
  obtain ⟨p, q, l, hp, hq, hl, hX, e⟩ := sch_parts hr
  obtain ⟨a, ha, haR⟩ := t0_mem q hq
  obtain ⟨b, hb, hbR⟩ := t0_mem p hp
  have hu := repC_G hl
  refine ⟨a⁻¹ * (elemW (classz.centGens.getD l []) * b),
    mul_mem (inv_mem ha) (mul_mem (gen_mem hl) hb), repC_of_pt hX fun x hx => ?_⟩
  have hy : pt (S r) x < 1408 := pt_lt hX hx
  have h1 : pt (pc (T0 q) (S r)) x = (a ⟨pt (S r) x, hy⟩).val := by
    rw [pt_pc haR.1 hx, repC_pt haR hy]
  have h2 : pt (pc (G l) (T0 p)) x =
      ((elemW (classz.centGens.getD l []) * b) ⟨x, hx⟩).val := by
    rw [← repC_pt (repC_pc hu hbR) hx]
  rw [e, h2] at h1
  have h3 : a ⟨pt (S r) x, hy⟩ = (elemW (classz.centGens.getD l []) * b) ⟨x, hx⟩ :=
    Fin.ext h1.symm
  rw [Equiv.Perm.mul_apply, ← h3]
  simp

theorem t1K_parts {S T1 P1 : Nat → Nat} {j : Nat} (h : t1K S T1 P1 j = true) :
    pt (T1 j) 0 = 0 ∧ (∀ j' < j, pt (T1 j) 1 ≠ pt (T1 j') 1) ∧
      (j ≠ 0 → ∃ p r, p < j ∧ r < nS ∧ T1 j = pc (S r) (T1 p)) := by
  unfold t1K at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  refine ⟨Nat.eq_of_beq_eq_true a, fun j' hj' => ?_, fun h0 => ?_⟩
  · have h' := mkNot (allN_spec b j' hj')
    exact fun e => by rw [e] at h'; simp at h'
  · have e0 : Nat.beq j 0 = false := Bool.eq_false_iff.2 fun h'' => h0 (Nat.eq_of_beq_eq_true h'')
    rw [e0] at h
    simp only [strictB_app] at h
    obtain ⟨c, h⟩ := mkA h
    obtain ⟨d, f⟩ := mkA h
    exact ⟨_, _, Nat.blt_eq.mp c, Nat.blt_eq.mp d, Nat.eq_of_beq_eq_true f⟩

theorem t1_parts {j : Nat} (hj : j < 24) :
    pt (T1 j) 0 = 0 ∧ (∀ j' < j, pt (T1 j) 1 ≠ pt (T1 j') 1) ∧
      (j ≠ 0 → ∃ p r, p < j ∧ r < nS ∧ T1 j = pc (S r) (T1 p)) :=
  t1K_parts (allN_spec czT_t1 j hj)

theorem t1_mem : ∀ j < 24, ∃ g ∈ czC, RepC (T1 j) g := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h0 : j = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [head_parts.2.2.2]; exact repC_idK⟩
    · obtain ⟨p, r, hp, hr, e⟩ := (t1_parts hj).2.2 h0
      obtain ⟨g, hg, hgR⟩ := ih p hp (by omega)
      obtain ⟨s, hs, hsR⟩ := s_mem hr
      exact ⟨_, mul_mem hs hg, by rw [e]; exact repC_pc hsR hgR⟩

noncomputable def t0P (i : Nat) : Equiv.Perm (Fin 1408) :=
  if h : i < 1280 then (t0_mem i h).choose else 1

noncomputable def t1P (j : Nat) : Equiv.Perm (Fin 1408) :=
  if h : j < 24 then (t1_mem j h).choose else 1

theorem t0P_spec {i : Nat} (hi : i < 1280) : t0P i ∈ czC ∧ RepC (T0 i) (t0P i) := by
  rw [t0P, dif_pos hi]
  exact (t0_mem i hi).choose_spec

theorem t1P_spec {j : Nat} (hj : j < 24) : t1P j ∈ czC ∧ RepC (T1 j) (t1P j) := by
  rw [t1P, dif_pos hj]
  exact (t1_mem j hj).choose_spec

theorem t0P_zero {i : Nat} (hi : i < 1280) :
    (t0P i ⟨0, by norm_num⟩).val = pt (T0 i) 0 :=
  (repC_pt (t0P_spec hi).2 (by norm_num)).symm

theorem t1P_zero {j : Nat} (hj : j < 24) : t1P j ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
  Fin.ext (by rw [← repC_pt (t1P_spec hj).2 (by norm_num), (t1_parts hj).1])

theorem t1P_one {j : Nat} (hj : j < 24) :
    (t1P j ⟨1, by norm_num⟩).val = pt (T1 j) 1 :=
  (repC_pt (t1P_spec hj).2 (by norm_num)).symm

theorem keys_lt {i i' : Nat} (h : i < i') (hi' : i' < 1280) : pt (T0 i) 0 < pt (T0 i') 0 := by
  have hk := czT_keys
  unfold keysK at hk
  induction i' with
  | zero => omega
  | succ i' ih =>
    have hs : pt (T0 i') 0 < pt (T0 (i' + 1)) 0 :=
      Nat.blt_eq.mp (allN_spec hk i' (by unfold n0; simp only [Nat.sub_eq]; omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact (ih h' (by omega)).trans hs
    · rw [h']
      exact hs

theorem t0P_inj {i i' : Nat} (hi : i < 1280) (hi' : i' < 1280)
    (h : t0P i ⟨0, by norm_num⟩ = t0P i' ⟨0, by norm_num⟩) : i = i' := by
  have e := congrArg Fin.val h
  rw [t0P_zero hi, t0P_zero hi'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd e (keys_lt hlt hi').ne
  · exact absurd e (keys_lt hlt hi).ne'

theorem t1P_inj {j j' : Nat} (hj : j < 24) (hj' : j' < 24)
    (h : t1P j ⟨1, by norm_num⟩ = t1P j' ⟨1, by norm_num⟩) : j = j' := by
  have e := congrArg Fin.val h
  rw [t1P_one hj, t1P_one hj'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (t1_parts hj').2.1 j hlt e.symm
  · exact (t1_parts hj).2.1 j' hlt e

theorem el_inj {i i' j j' : Nat} (hi : i < 1280) (hi' : i' < 1280) (hj : j < 24) (hj' : j' < 24)
    (h : t0P i * t1P j = t0P i' * t1P j') : i = i' ∧ j = j' := by
  have h0 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨0, by norm_num⟩) h
  simp only [Equiv.Perm.mul_apply, t1P_zero hj, t1P_zero hj'] at h0
  have ei := t0P_inj hi hi' h0
  subst ei
  have h1 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨1, by norm_num⟩) h
  simp only [Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq] at h1
  exact ⟨rfl, t1P_inj hj hj' h1⟩

theorem card_ge : 30720 ≤ Nat.card czC := by
  classical
  let E : Finset (Equiv.Perm (Fin 1408)) :=
    (Finset.range 1280 ×ˢ Finset.range 24).image fun p => t0P p.1 * t1P p.2
  have hinj : Set.InjOn (fun p : Nat × Nat => t0P p.1 * t1P p.2)
      ↑(Finset.range 1280 ×ˢ Finset.range 24) := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' e
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hp'
    obtain ⟨h1, h2⟩ := el_inj hp.1 hp'.1 hp.2 hp'.2 e
    rw [h1, h2]
  have hE : E.card = 30720 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
      Finset.card_range]
  have hsub : (↑E : Set (Equiv.Perm (Fin 1408))) ⊆ (czC : Set (Equiv.Perm (Fin 1408))) := by
    intro x hx
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mul_mem (t0P_spec hp.1).1 (t1P_spec hp.2).1
  have hc : Nat.card czC = (czC : Set (Equiv.Perm (Fin 1408))).ncard := Nat.card_coe_set_eq _
  rw [hc, ← hE, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem le_cent : czC ≤ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨elemW_mem w, ?_⟩
  obtain ⟨l, hl, rfl⟩ : ∃ l < 2, classz.centGens.getD l [] = w := by
    have hw' : w ∈ classz.centGens := hw
    simp only [classz, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  change elemW (classz.centGens.getD l []) ∈ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  have hz : RepC (WK wordZ) elemZ := repC_word (by decide)
  have hc := Nat.eq_of_beq_eq_true (head_parts.2.1 l hl)
  have h1 := repC_pc (repC_G hl) hz
  have h2 := repC_pc hz (repC_G hl)
  rw [hc] at h1
  exact eq_of_repC h2 h1

theorem class_ge {w : List Nat} (hw : lettersOK w = true) {R P S W : Nat → Nat} {n cnt : Nat}
    (h : clsK w R P S W n cnt = true) : cnt ≤ (conjClass P1408 (elemW w)).ncard := by
  obtain ⟨-, -, hs, -⟩ := clsK_parts h
  have hreps := reps_mem hw h
  have H : ∀ i, ∃ r : Equiv.Perm (Fin 1408), i < n → r ∈ conjClass P1408 (elemW w) ∧
      RepC (R i) r := by
    intro i
    by_cases hi : i < n
    · obtain ⟨c, hcP, hcR⟩ := hreps i hi
      exact ⟨_, fun _ => ⟨⟨c, hcP, rfl⟩, hcR⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose r hr using H
  have hS : ∀ m < cnt, f16 (S m) 0 < n ∧ f16 (S m) 1 < 11 := by
    intro m hm
    have h1 := allN_spec hs m hm
    simp only [strictB_app] at h1
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, -⟩ := mkA h1
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b⟩
  obtain ⟨e, he⟩ : ∃ e : Nat → Equiv.Perm (Fin 1408), ∀ m, e m =
      elemW y0Word ^ f16 (S m) 1 * r (f16 (S m) 0) * (elemW y0Word ^ f16 (S m) 1)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hkey : ∀ m < cnt, keyK (R (f16 (S m) 0)) (f16 (S m) 1) = keyP (e m) := by
    intro m hm
    rw [he m]
    exact keyK_eq (hr _ (hS m hm).1).2 (by have := (hS m hm).2; omega)
  have hsucc : ∀ m, m + 1 < cnt → keyP (e m) < keyP (e (m + 1)) := by
    intro m hm
    have h1 := allN_spec hs m (by omega)
    simp only [strictB_app] at h1
    obtain ⟨-, h1⟩ := mkA h1
    obtain ⟨-, h1⟩ := mkA h1
    have e1 : Nat.blt (m + 1) cnt = true := Nat.blt_eq.mpr hm
    rw [e1] at h1
    rw [← hkey m (by omega), ← hkey (m + 1) hm]
    exact Nat.blt_eq.mp h1
  have hmono : ∀ m m', m < m' → m' < cnt → keyP (e m) < keyP (e m') := by
    intro m m' hlt hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
      · exact (ih h' (by omega)).trans (hsucc m' hm')
      · rw [h']
        exact hsucc m' hm'
  have hinj : Set.InjOn e ↑(Finset.range cnt) := by
    intro m hm m' hm' hee
    have hm1 : m < cnt := Finset.mem_range.1 hm
    have hm2 : m' < cnt := Finset.mem_range.1 hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono m m' hlt hm2
      rw [hee] at h1
      exact lt_irrefl _ h1
    · have h1 := hmono m' m hlt hm1
      rw [hee] at h1
      exact lt_irrefl _ h1
  have hsub : (↑((Finset.range cnt).image e) : Set (Equiv.Perm (Fin 1408))) ⊆
      conjClass P1408 (elemW w) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
    have hm1 : m < cnt := Finset.mem_range.1 hm
    obtain ⟨⟨c, hcP, hcr⟩, -⟩ := hr _ (hS m hm1).1
    refine ⟨elemW y0Word ^ f16 (S m) 1 * c, mul_mem (pow_mem (elemW_mem _) _) hcP, ?_⟩
    rw [he m, hcr]
    group
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, Finset.card_range] at h1

theorem class_z_ge : 5775 ≤ (conjClass P1408 elemZ).ncard := by
  have hz : elemW classz.rep = elemZ := by
    have e : classz.rep = wordZ := by decide
    rw [e]
    rfl
  rw [← hz]
  exact class_ge (by decide) kCZ

theorem czT_eq (hP : Nat.card ↥P1408 = 177408000) :
    czC = P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧ Nat.card czC = 30720 := by
  have hm := ncard_conjClass_mul_card P1408 elemZ
  rw [hP] at hm
  have hK : Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) ≤ 30720 := by
    by_contra hlt
    have h1 : 5775 * 30721 ≤ (conjClass P1408 elemZ).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul class_z_ge (by omega)
    omega
  have hle := Subgroup.card_le_of_le le_cent
  have hge := card_ge
  exact ⟨Subgroup.eq_of_le_of_card_ge le_cent (by omega), by omega⟩

theorem mem_iff (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)} :
    g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ↔
      ∃ i < 1280, ∃ j < 24, g = t0P i * t1P j := by
  classical
  obtain ⟨hC, hcard⟩ := czT_eq hP
  rw [← hC]
  let E : Finset (Equiv.Perm (Fin 1408)) :=
    (Finset.range 1280 ×ˢ Finset.range 24).image fun p => t0P p.1 * t1P p.2
  have hinj : Set.InjOn (fun p : Nat × Nat => t0P p.1 * t1P p.2)
      ↑(Finset.range 1280 ×ˢ Finset.range 24) := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' e
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hp'
    obtain ⟨h1, h2⟩ := el_inj hp.1 hp'.1 hp.2 hp'.2 e
    rw [h1, h2]
  have hE : E.card = 30720 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
      Finset.card_range]
  have hsub : (↑E : Set (Equiv.Perm (Fin 1408))) ⊆ (czC : Set (Equiv.Perm (Fin 1408))) := by
    intro x hx
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mul_mem (t0P_spec hp.1).1 (t1P_spec hp.2).1
  have hc : (czC : Set (Equiv.Perm (Fin 1408))).ncard = 30720 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq : (↑E : Set (Equiv.Perm (Fin 1408))) = (czC : Set (Equiv.Perm (Fin 1408))) :=
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
    exact mul_mem (t0P_spec hi).1 (t1P_spec hj).1

theorem t0P_zero_one : t0P 0 = 1 :=
  eq_of_repC (t0P_spec (by norm_num)).2 (by rw [head_parts.2.2.1]; exact repC_idK)

theorem t1P_zero_one : t1P 0 = 1 :=
  eq_of_repC (t1P_spec (by norm_num)).2 (by rw [head_parts.2.2.2]; exact repC_idK)

theorem base (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (h0 : g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩) (h1 : g ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩) :
    g = 1 := by
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
  have e0 : t0P i ⟨0, by norm_num⟩ = t0P 0 ⟨0, by norm_num⟩ := by
    rw [Equiv.Perm.mul_apply, t1P_zero hj] at h0
    rw [t0P_zero_one, Equiv.Perm.one_apply]
    exact h0
  have ei := t0P_inj hi (by norm_num) e0
  subst ei
  rw [t0P_zero_one, one_mul] at h1 ⊢
  have e1 : t1P j ⟨1, by norm_num⟩ = t1P 0 ⟨1, by norm_num⟩ := by
    rw [t1P_zero_one, Equiv.Perm.one_apply, h1]
  have ej := t1P_inj hj (by norm_num) e1
  rw [ej, t1P_zero_one]

theorem eq_of_base (hP : Nat.card ↥P1408 = 177408000) {g h : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (hh : h ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))
    (h0 : g ⟨0, by norm_num⟩ = h ⟨0, by norm_num⟩) (h1 : g ⟨1, by norm_num⟩ = h ⟨1, by norm_num⟩) :
    g = h := by
  have e := base hP (mul_mem (inv_mem hh) hg) (by rw [Equiv.Perm.mul_apply, h0]; simp)
    (by rw [Equiv.Perm.mul_apply, h1]; simp)
  rw [inv_mul_eq_one] at e
  exact e.symm

theorem cent_az (ha : ∀ g ∈ P1408, elemA * g = g * elemA) :
    P1408 ⊓ centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) =
      P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · rintro ⟨hgP, hg⟩
    refine ⟨hgP, ?_⟩
    have h2 : elemA * (elemZ * g) = elemA * (g * elemZ) := by
      rw [← mul_assoc, hg, ← mul_assoc, ← ha g hgP, mul_assoc]
    exact mul_left_cancel h2
  · rintro ⟨hgP, hg⟩
    refine ⟨hgP, ?_⟩
    rw [mul_assoc, hg, ← mul_assoc, ha g hgP, mul_assoc]

end CFSG.KD.HN1408.CzT

end
