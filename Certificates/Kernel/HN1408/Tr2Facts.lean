
module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.Tr2Defs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tr2

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev genC (ws : List (List Nat)) : Subgroup (Equiv.Perm (Fin 1408)) :=
  closure (elemW '' {w | w ∈ ws})

structure Tr2OK (ws : List (List Nat)) (Zw : List Nat) (n0 n1 nS : Nat)
    (G T0 P0 S SR T1 P1 : Nat → Nat) : Prop where
  letters : ∀ l < ws.length, lettersOK (ws.getD l []) = true
  zw : lettersOK Zw = true
  head : headK ws Zw G T0 T1 = true
  keys : keysK n0 T0 = true
  tree : allN n0 (treeK ws.length n0 G T0 P0) = true
  sch : allN nS (schK ws.length n0 G T0 S SR) = true
  t1 : allN n1 (t1K nS S T1 P1) = true

variable {ws : List (List Nat)} {Zw : List Nat} {n0 n1 nS : Nat} {G T0 P0 S SR T1 P1 : Nat → Nat}

theorem repC_idK : RepC idK 1 := ⟨cId, by rw [← idT_eq]; exact Rep.idT (by norm_num)⟩

theorem repC_of_pt {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (h : ∀ x (hx : x < 1408), pt X x = (g ⟨x, hx⟩).val) : RepC X g :=
  ⟨hX, fun x hx => by rw [ap_eq hX hx, h x hx, idx_of_lt g hx, Equiv.Perm.smul_def]⟩

theorem gen_mem {l : Nat} (hl : l < ws.length) : elemW (ws.getD l []) ∈ genC ws := by
  refine subset_closure ⟨_, ?_, rfl⟩
  change ws.getD l [] ∈ ws
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem hl

theorem headK_parts (h : headK ws Zw G T0 T1 = true) :
    (∀ l < ws.length, G l = WK (ws.getD l [])) ∧ (∀ l < ws.length, commP (G l) (WK Zw) = true) ∧
      T0 0 = idK ∧ T1 0 = idK := by
  unfold headK at h
  generalize WK Zw = Z at h ⊢
  obtain ⟨h1, h⟩ := mkA h
  obtain ⟨h2, h⟩ := mkA h
  obtain ⟨h3, h4⟩ := mkA h
  rw [strictB_app] at h2
  exact ⟨fun l hl => Nat.eq_of_beq_eq_true (allN_spec h1 l hl), fun l hl => allN_spec h2 l hl,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem repC_G (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1) {l : Nat} (hl : l < ws.length) :
    RepC (G l) (elemW (ws.getD l [])) := by
  rw [(headK_parts h.head).1 l hl]
  exact repC_word (h.letters l hl)

theorem treeK_parts {m : Nat} {i : Nat} (h : treeK m n0 G T0 P0 i = true) (h0 : i ≠ 0) :
    ∃ p l, p < n0 ∧ l < m ∧ fd (P0 i) 2 = fd (P0 p) 2 + 1 ∧ T0 i = pc (G l) (T0 p) := by
  unfold treeK at h
  have e0 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h'' => h0 (Nat.eq_of_beq_eq_true h'')
  rw [e0] at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨_, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d⟩

theorem t0_mem (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1) :
    ∀ i < n0, ∃ g ∈ genC ws, RepC (T0 i) g := by
  suffices H : ∀ d i, fd (P0 i) 2 = d → i < n0 → ∃ g ∈ genC ws, RepC (T0 i) g from
    fun i hi => H _ i rfl hi
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hd hi
    by_cases h0 : i = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [(headK_parts h.head).2.2.1]; exact repC_idK⟩
    · obtain ⟨p, l, hp, hl, hdp, e⟩ := treeK_parts (allN_spec h.tree i hi) h0
      obtain ⟨g, hg, hgR⟩ := ih _ (by omega) p rfl hp
      exact ⟨_, mul_mem (gen_mem hl) hg, by rw [e]; exact repC_pc (repC_G h hl) hgR⟩

theorem schK_parts {m r : Nat} (h : schK m n0 G T0 S SR r = true) :
    ∃ p q l, p < n0 ∧ q < n0 ∧ l < m ∧ Cn (S r) ∧ pc (T0 q) (S r) = pc (G l) (T0 p) := by
  unfold schK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  exact ⟨_, _, _, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.blt_eq.mp d, a, Nat.eq_of_beq_eq_true f⟩

theorem s_mem (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1) {r : Nat} (hr : r < nS) :
    ∃ g ∈ genC ws, RepC (S r) g := by
  obtain ⟨p, q, l, hp, hq, hl, hX, e⟩ := schK_parts (allN_spec h.sch r hr)
  obtain ⟨a, ha, haR⟩ := t0_mem h q hq
  obtain ⟨b, hb, hbR⟩ := t0_mem h p hp
  have hu := repC_G h hl
  refine ⟨a⁻¹ * (elemW (ws.getD l []) * b),
    mul_mem (inv_mem ha) (mul_mem (gen_mem hl) hb), repC_of_pt hX fun x hx => ?_⟩
  have hy : pt (S r) x < 1408 := pt_lt hX hx
  have h1 : pt (pc (T0 q) (S r)) x = (a ⟨pt (S r) x, hy⟩).val := by
    rw [pt_pc haR.1 hx, repC_pt haR hy]
  have h2 : pt (pc (G l) (T0 p)) x = ((elemW (ws.getD l []) * b) ⟨x, hx⟩).val := by
    rw [← repC_pt (repC_pc hu hbR) hx]
  rw [e, h2] at h1
  have h3 : a ⟨pt (S r) x, hy⟩ = (elemW (ws.getD l []) * b) ⟨x, hx⟩ := Fin.ext h1.symm
  rw [Equiv.Perm.mul_apply, ← h3]
  simp

theorem t1K_parts {j : Nat} (h : t1K nS S T1 P1 j = true) :
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

theorem t1_mem (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1) :
    ∀ j < n1, ∃ g ∈ genC ws, RepC (T1 j) g := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h0 : j = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [(headK_parts h.head).2.2.2]; exact repC_idK⟩
    · obtain ⟨p, r, hp, hr, e⟩ := (t1K_parts (allN_spec h.t1 j hj)).2.2 h0
      obtain ⟨g, hg, hgR⟩ := ih p hp (by omega)
      obtain ⟨s, hs, hsR⟩ := s_mem h hr
      exact ⟨_, mul_mem hs hg, by rw [e]; exact repC_pc hsR hgR⟩

noncomputable def t0P (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1) (i : Nat) :
    Equiv.Perm (Fin 1408) :=
  if hi : i < n0 then (t0_mem h i hi).choose else 1

noncomputable def t1P (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1) (j : Nat) :
    Equiv.Perm (Fin 1408) :=
  if hj : j < n1 then (t1_mem h j hj).choose else 1

variable (h : Tr2OK ws Zw n0 n1 nS G T0 P0 S SR T1 P1)
include h

theorem t0P_spec {i : Nat} (hi : i < n0) : t0P h i ∈ genC ws ∧ RepC (T0 i) (t0P h i) := by
  rw [t0P, dif_pos hi]
  exact (t0_mem h i hi).choose_spec

theorem t1P_spec {j : Nat} (hj : j < n1) : t1P h j ∈ genC ws ∧ RepC (T1 j) (t1P h j) := by
  rw [t1P, dif_pos hj]
  exact (t1_mem h j hj).choose_spec

theorem t0P_zero {i : Nat} (hi : i < n0) : (t0P h i ⟨0, by norm_num⟩).val = pt (T0 i) 0 :=
  (repC_pt (t0P_spec h hi).2 (by norm_num)).symm

theorem t1P_zero {j : Nat} (hj : j < n1) : t1P h j ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
  Fin.ext (by rw [← repC_pt (t1P_spec h hj).2 (by norm_num), (t1K_parts (allN_spec h.t1 j hj)).1])

theorem t1P_one {j : Nat} (hj : j < n1) : (t1P h j ⟨1, by norm_num⟩).val = pt (T1 j) 1 :=
  (repC_pt (t1P_spec h hj).2 (by norm_num)).symm

theorem keys_lt {i i' : Nat} (hlt : i < i') (hi' : i' < n0) : pt (T0 i) 0 < pt (T0 i') 0 := by
  have hk := h.keys
  unfold keysK at hk
  induction i' with
  | zero => omega
  | succ i' ih =>
    have hs : pt (T0 i') 0 < pt (T0 (i' + 1)) 0 :=
      Nat.blt_eq.mp (allN_spec hk i' (by simp only [Nat.sub_eq]; omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
    · exact (ih h' (by omega)).trans hs
    · rw [h']
      exact hs

theorem t0P_inj {i i' : Nat} (hi : i < n0) (hi' : i' < n0)
    (he : t0P h i ⟨0, by norm_num⟩ = t0P h i' ⟨0, by norm_num⟩) : i = i' := by
  have e := congrArg Fin.val he
  rw [t0P_zero h hi, t0P_zero h hi'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd e (keys_lt h hlt hi').ne
  · exact absurd e (keys_lt h hlt hi).ne'

theorem t1P_inj {j j' : Nat} (hj : j < n1) (hj' : j' < n1)
    (he : t1P h j ⟨1, by norm_num⟩ = t1P h j' ⟨1, by norm_num⟩) : j = j' := by
  have e := congrArg Fin.val he
  rw [t1P_one h hj, t1P_one h hj'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (t1K_parts (allN_spec h.t1 j' hj')).2.1 j hlt e.symm
  · exact (t1K_parts (allN_spec h.t1 j hj)).2.1 j' hlt e

theorem el_inj {i i' j j' : Nat} (hi : i < n0) (hi' : i' < n0) (hj : j < n1) (hj' : j' < n1)
    (he : t0P h i * t1P h j = t0P h i' * t1P h j') : i = i' ∧ j = j' := by
  have h0 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨0, by norm_num⟩) he
  simp only [Equiv.Perm.mul_apply, t1P_zero h hj, t1P_zero h hj'] at h0
  have ei := t0P_inj h hi hi' h0
  subst ei
  have h1 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨1, by norm_num⟩) he
  simp only [Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq] at h1
  exact ⟨rfl, t1P_inj h hj hj' h1⟩

theorem card_ge : n0 * n1 ≤ Nat.card (genC ws) := by
  classical
  let E : Finset (Equiv.Perm (Fin 1408)) :=
    (Finset.range n0 ×ˢ Finset.range n1).image fun p => t0P h p.1 * t1P h p.2
  have hinj : Set.InjOn (fun p : Nat × Nat => t0P h p.1 * t1P h p.2)
      ↑(Finset.range n0 ×ˢ Finset.range n1) := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' e
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hp'
    obtain ⟨h1, h2⟩ := el_inj h hp.1 hp'.1 hp.2 hp'.2 e
    rw [h1, h2]
  have hE : E.card = n0 * n1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
      Finset.card_range]
  have hsub : (↑E : Set (Equiv.Perm (Fin 1408))) ⊆ (genC ws : Set (Equiv.Perm (Fin 1408))) := by
    intro x hx
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mul_mem (t0P_spec h hp.1).1 (t1P_spec h hp.2).1
  have hc : Nat.card (genC ws) = (genC ws : Set (Equiv.Perm (Fin 1408))).ncard :=
    Nat.card_coe_set_eq _
  rw [hc, ← hE, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem le_cent : genC ws ≤ P1408 ⊓ centralizer ({elemW Zw} : Set (Equiv.Perm (Fin 1408))) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨elemW_mem w, ?_⟩
  obtain ⟨l, hl, rfl⟩ : ∃ l < ws.length, ws.getD l [] = w := by
    have hw' : w ∈ ws := hw
    obtain ⟨l, hl, e⟩ := List.getElem_of_mem hw'
    exact ⟨l, hl, by rw [List.getD_eq_getElem _ _ hl, e]⟩
  change elemW (ws.getD l []) ∈ centralizer ({elemW Zw} : Set (Equiv.Perm (Fin 1408)))
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  have hz : RepC (WK Zw) (elemW Zw) := repC_word h.zw
  have hc := Nat.eq_of_beq_eq_true ((headK_parts h.head).2.1 l hl)
  have h1 := repC_pc (repC_G h hl) hz
  have h2 := repC_pc hz (repC_G h hl)
  rw [hc] at h1
  exact eq_of_repC h2 h1

end CFSG.KD.HN1408.Tr2

end
