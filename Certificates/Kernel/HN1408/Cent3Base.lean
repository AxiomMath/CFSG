module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.Cent3Chk

@[expose] public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev cC : Subgroup (Equiv.Perm (Fin 1408)) := closure (elemW '' {w | w ∈ fix3.cent})

theorem repC_idK : RepC idK 1 := ⟨cId, by rw [← idT_eq]; exact Rep.idT (by norm_num)⟩

theorem repC_of_pt {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (h : ∀ x (hx : x < 1408), pt X x = (g ⟨x, hx⟩).val) : RepC X g :=
  ⟨hX, fun x hx => by rw [ap_eq hX hx, h x hx, idx_of_lt g hx, Equiv.Perm.smul_def]⟩

theorem gen_word {l : Nat} (hl : l < 4) : fix3.cent.getD l [] ∈ fix3.cent := by
  interval_cases l <;> decide

theorem gen_letters {l : Nat} (hl : l < 4) : lettersOK (fix3.cent.getD l []) = true := by
  interval_cases l <;> decide

theorem gen_mem {l : Nat} (hl : l < 4) : elemW (fix3.cent.getD l []) ∈ cC :=
  subset_closure ⟨_, gen_word hl, rfl⟩

theorem headK_parts {G T0 T1 : Nat → Nat} (h : headK G T0 T1 = true) :
    (∀ l < 4, G l = WK (fix3.cent.getD l [])) ∧ T0 0 = idK ∧ T1 0 = idK := by
  unfold headK at h
  obtain ⟨h1, h⟩ := mkA h
  obtain ⟨h3, h4⟩ := mkA h
  exact ⟨fun l hl => Nat.eq_of_beq_eq_true (allN_spec h1 l hl), Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4⟩

theorem head_parts :
    (∀ l < 4, G l = WK (fix3.cent.getD l [])) ∧ T0 0 = idK ∧ T1 0 = idK :=
  headK_parts ch441603_head

theorem repC_G {l : Nat} (hl : l < 4) : RepC (G l) (elemW (fix3.cent.getD l [])) := by
  rw [head_parts.1 l hl]
  exact repC_word (gen_letters hl)

theorem treeK_parts {G T0 P0 : Nat → Nat} {i : Nat} (h : treeK G T0 P0 i = true) (h0 : i ≠ 0) :
    ∃ p l, p < 40 ∧ l < 4 ∧ fd (P0 i) 2 = fd (P0 p) 2 + 1 ∧ T0 i = pc (G l) (T0 p) := by
  unfold treeK at h
  have e0 : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h'' => h0 (Nat.eq_of_beq_eq_true h'')
  rw [e0] at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨_, _, Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d⟩

theorem t0_mem : ∀ i < 40, ∃ g ∈ cC, RepC (T0 i) g := by
  suffices H : ∀ d i, fd (P0 i) 2 = d → i < 40 → ∃ g ∈ cC, RepC (T0 i) g from
    fun i hi => H _ i rfl hi
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i hd hi
    by_cases h0 : i = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [head_parts.2.1]; exact repC_idK⟩
    · obtain ⟨p, l, hp, hl, hdp, e⟩ := treeK_parts (allN_spec ch441603_tree i hi) h0
      obtain ⟨g, hg, hgR⟩ := ih _ (by omega) p rfl hp
      exact ⟨_, mul_mem (gen_mem hl) hg, by rw [e]; exact repC_pc (repC_G hl) hgR⟩

theorem schK_parts {G T0 S SR : Nat → Nat} {r : Nat} (h : schK G T0 S SR r = true) :
    ∃ p q l, p < 40 ∧ q < 40 ∧ l < 4 ∧ Cn (S r) ∧ pc (T0 q) (S r) = pc (G l) (T0 p) := by
  unfold schK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  exact ⟨_, _, _, Nat.blt_eq.mp b, Nat.blt_eq.mp c, Nat.blt_eq.mp d, a, Nat.eq_of_beq_eq_true f⟩

theorem s_mem {r : Nat} (hr : r < 3) : ∃ g ∈ cC, RepC (S r) g := by
  obtain ⟨p, q, l, hp, hq, hl, hX, e⟩ := schK_parts (allN_spec ch441603_sch r hr)
  obtain ⟨a, ha, haR⟩ := t0_mem q hq
  obtain ⟨b, hb, hbR⟩ := t0_mem p hp
  have hu := repC_G hl
  refine ⟨a⁻¹ * (elemW (fix3.cent.getD l []) * b),
    mul_mem (inv_mem ha) (mul_mem (gen_mem hl) hb), repC_of_pt hX fun x hx => ?_⟩
  have hy : pt (S r) x < 1408 := pt_lt hX hx
  have h1 : pt (pc (T0 q) (S r)) x = (a ⟨pt (S r) x, hy⟩).val := by
    rw [pt_pc haR.1 hx, repC_pt haR hy]
  have h2 : pt (pc (G l) (T0 p)) x =
      ((elemW (fix3.cent.getD l []) * b) ⟨x, hx⟩).val := by
    rw [← repC_pt (repC_pc hu hbR) hx]
  rw [e, h2] at h1
  have h3 : a ⟨pt (S r) x, hy⟩ = (elemW (fix3.cent.getD l []) * b) ⟨x, hx⟩ :=
    Fin.ext h1.symm
  rw [Equiv.Perm.mul_apply, ← h3]
  simp

theorem t1K_parts {S T1 P1 : Nat → Nat} {j : Nat} (h : t1K S T1 P1 j = true) :
    pt (T1 j) 0 = 0 ∧ (∀ j' < j, pt (T1 j) 1 ≠ pt (T1 j') 1) ∧
      (j ≠ 0 → ∃ p r, p < j ∧ r < 3 ∧ T1 j = pc (S r) (T1 p)) := by
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

theorem t1_parts {j : Nat} (hj : j < 36) :
    pt (T1 j) 0 = 0 ∧ (∀ j' < j, pt (T1 j) 1 ≠ pt (T1 j') 1) ∧
      (j ≠ 0 → ∃ p r, p < j ∧ r < 3 ∧ T1 j = pc (S r) (T1 p)) :=
  t1K_parts (allN_spec ch441603_t1 j hj)

theorem t1_mem : ∀ j < 36, ∃ g ∈ cC, RepC (T1 j) g := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h0 : j = 0
    · subst h0
      exact ⟨1, one_mem _, by rw [head_parts.2.2]; exact repC_idK⟩
    · obtain ⟨p, r, hp, hr, e⟩ := (t1_parts hj).2.2 h0
      obtain ⟨g, hg, hgR⟩ := ih p hp (by omega)
      obtain ⟨s, hs, hsR⟩ := s_mem hr
      exact ⟨_, mul_mem hs hg, by rw [e]; exact repC_pc hsR hgR⟩

noncomputable def t0P (i : Nat) : Equiv.Perm (Fin 1408) :=
  if h : i < 40 then (t0_mem i h).choose else 1

noncomputable def t1P (j : Nat) : Equiv.Perm (Fin 1408) :=
  if h : j < 36 then (t1_mem j h).choose else 1

theorem t0P_spec {i : Nat} (hi : i < 40) : t0P i ∈ cC ∧ RepC (T0 i) (t0P i) := by
  rw [t0P, dif_pos hi]
  exact (t0_mem i hi).choose_spec

theorem t1P_spec {j : Nat} (hj : j < 36) : t1P j ∈ cC ∧ RepC (T1 j) (t1P j) := by
  rw [t1P, dif_pos hj]
  exact (t1_mem j hj).choose_spec

theorem t0P_zero {i : Nat} (hi : i < 40) : (t0P i ⟨0, by norm_num⟩).val = pt (T0 i) 0 :=
  (repC_pt (t0P_spec hi).2 (by norm_num)).symm

theorem t1P_zero {j : Nat} (hj : j < 36) : t1P j ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
  Fin.ext (by rw [← repC_pt (t1P_spec hj).2 (by norm_num), (t1_parts hj).1])

theorem t1P_one {j : Nat} (hj : j < 36) : (t1P j ⟨1, by norm_num⟩).val = pt (T1 j) 1 :=
  (repC_pt (t1P_spec hj).2 (by norm_num)).symm

theorem keys_lt {i i' : Nat} (h : i < i') (hi' : i' < 40) : pt (T0 i) 0 < pt (T0 i') 0 := by
  have hk := ch441603_keys
  unfold keysK at hk
  induction i' with
  | zero => omega
  | succ i' ih =>
    have hs : pt (T0 i') 0 < pt (T0 (i' + 1)) 0 := Nat.blt_eq.mp (allN_spec hk i' (by omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact (ih h' (by omega)).trans hs
    · rw [h']
      exact hs

theorem t0P_inj {i i' : Nat} (hi : i < 40) (hi' : i' < 40)
    (h : t0P i ⟨0, by norm_num⟩ = t0P i' ⟨0, by norm_num⟩) : i = i' := by
  have e := congrArg Fin.val h
  rw [t0P_zero hi, t0P_zero hi'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd e (keys_lt hlt hi').ne
  · exact absurd e (keys_lt hlt hi).ne'

theorem t1P_inj {j j' : Nat} (hj : j < 36) (hj' : j' < 36)
    (h : t1P j ⟨1, by norm_num⟩ = t1P j' ⟨1, by norm_num⟩) : j = j' := by
  have e := congrArg Fin.val h
  rw [t1P_one hj, t1P_one hj'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (t1_parts hj').2.1 j hlt e.symm
  · exact (t1_parts hj).2.1 j' hlt e

noncomputable def el (k : Nat) : Equiv.Perm (Fin 1408) := t0P (k / 36) * t1P (k % 36)

theorem el_mem {k : Nat} (hk : k < 1440) : el k ∈ cC :=
  mul_mem (t0P_spec (by omega)).1 (t1P_spec (Nat.mod_lt _ (by norm_num))).1

theorem repC_el {k : Nat} (hk : k < 1440) : RepC (elK k) (el k) := by
  have e : elK k = pc (T0 (k / 36)) (T1 (k % 36)) := rfl
  rw [e]
  exact repC_pc (t0P_spec (i := k / 36) (by omega)).2
    (t1P_spec (j := k % 36) (Nat.mod_lt _ (by norm_num))).2

theorem el_pt {k p : Nat} (hk : k < 1440) (hp : p < 1408) : (el k ⟨p, hp⟩).val = ev k p := by
  have h1 := repC_pt (t1P_spec (j := k % 36) (Nat.mod_lt _ (by norm_num))).2 hp
  have h2 := repC_pt (t0P_spec (i := k / 36) (by omega)).2 (Fin.isLt (t1P (k % 36) ⟨p, hp⟩))
  have e : ev k p = pt (T0 (k / 36)) (pt (T1 (k % 36)) p) := rfl
  rw [e, h1, h2, el, Equiv.Perm.mul_apply]

theorem ev_lt {k p : Nat} (hk : k < 1440) (hp : p < 1408) : ev k p < 1408 := by
  rw [← el_pt hk hp]
  exact Fin.isLt _

theorem el_apply {k p : Nat} (hk : k < 1440) (hp : p < 1408) :
    el k ⟨p, hp⟩ = ⟨ev k p, ev_lt hk hp⟩ :=
  Fin.ext (el_pt hk hp)

theorem el_inj {k k' : Nat} (hk : k < 1440) (hk' : k' < 1440) (h : el k = el k') : k = k' := by
  have hj : k % 36 < 36 := Nat.mod_lt _ (by norm_num)
  have hj' : k' % 36 < 36 := Nat.mod_lt _ (by norm_num)
  have h0 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨0, by norm_num⟩) h
  simp only [el, Equiv.Perm.mul_apply, t1P_zero hj, t1P_zero hj'] at h0
  have ei := t0P_inj (by omega) (by omega) h0
  have h1 := congrArg (fun g : Equiv.Perm (Fin 1408) => g ⟨1, by norm_num⟩) h
  simp only [el, Equiv.Perm.mul_apply] at h1
  rw [ei] at h1
  have ej := t1P_inj hj hj' ((t0P (k' / 36)).injective h1)
  omega

theorem t0P_zero_one : t0P 0 = 1 :=
  eq_of_repC (t0P_spec (by norm_num)).2 (by rw [head_parts.2.1]; exact repC_idK)

theorem t1P_zero_one : t1P 0 = 1 :=
  eq_of_repC (t1P_spec (by norm_num)).2 (by rw [head_parts.2.2]; exact repC_idK)

theorem el_zero : el 0 = 1 := by
  rw [el, Nat.zero_div, Nat.zero_mod, t0P_zero_one, t1P_zero_one, one_mul]

theorem exists_el (hC : Nat.card cC = 1440) {g : Equiv.Perm (Fin 1408)} (hg : g ∈ cC) :
    ∃ k < 1440, g = el k := by
  classical
  let E : Finset (Equiv.Perm (Fin 1408)) := (Finset.range 1440).image el
  have hinj : Set.InjOn el ↑(Finset.range 1440) := fun k hk k' hk' e =>
    el_inj (Finset.mem_range.1 hk) (Finset.mem_range.1 hk') e
  have hE : E.card = 1440 := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (↑E : Set (Equiv.Perm (Fin 1408))) ⊆ (cC : Set (Equiv.Perm (Fin 1408))) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact el_mem (Finset.mem_range.1 hk)
  have hc : (cC : Set (Equiv.Perm (Fin 1408))).ncard = 1440 := by
    rw [← Nat.card_coe_set_eq]
    exact hC
  have heq : (↑E : Set (Equiv.Perm (Fin 1408))) = (cC : Set (Equiv.Perm (Fin 1408))) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc, Set.ncard_coe_finset, hE]) (Set.toFinite _)
  have hg' : g ∈ (↑E : Set (Equiv.Perm (Fin 1408))) := by
    rw [heq]
    exact hg
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hg'
  exact ⟨k, Finset.mem_range.1 hk, rfl⟩

theorem eq_of_base (hC : Nat.card cC = 1440) {g h : Equiv.Perm (Fin 1408)} (hg : g ∈ cC)
    (hh : h ∈ cC) (h0 : g ⟨0, by norm_num⟩ = h ⟨0, by norm_num⟩)
    (h1 : g ⟨1, by norm_num⟩ = h ⟨1, by norm_num⟩) : g = h := by
  obtain ⟨k, hk, rfl⟩ := exists_el hC hg
  obtain ⟨k', hk', rfl⟩ := exists_el hC hh
  have hj : k % 36 < 36 := Nat.mod_lt _ (by norm_num)
  have hj' : k' % 36 < 36 := Nat.mod_lt _ (by norm_num)
  simp only [el, Equiv.Perm.mul_apply, t1P_zero hj, t1P_zero hj'] at h0
  have ei := t0P_inj (by omega) (by omega) h0
  simp only [el, Equiv.Perm.mul_apply] at h1
  rw [ei] at h1
  have ej := t1P_inj hj hj' ((t0P (k' / 36)).injective h1)
  have e : k = k' := by omega
  rw [e]

theorem eq_el (hC : Nat.card cC = 1440) {g : Equiv.Perm (Fin 1408)} (hg : g ∈ cC) {k : Nat}
    (hk : k < 1440) (h0 : (g ⟨0, by norm_num⟩).val = ev k 0)
    (h1 : (g ⟨1, by norm_num⟩).val = ev k 1) : g = el k :=
  eq_of_base hC hg (el_mem hk) (Fin.ext (by rw [h0, el_pt hk])) (Fin.ext (by rw [h1, el_pt hk]))

theorem base2_parts {f : Nat → Bool} (h : base2 f = true) : f 0 = true ∧ f 1 = true := mkA h

theorem el_mul (hC : Nat.card cC = 1440) {g h u : Nat} (hg : g < 1440) (hh : h < 1440)
    (hu : u < 1440) (hm : mulEq g h u = true) : el g * el h = el u := by
  obtain ⟨m0, m1⟩ := base2_parts hm
  refine eq_el hC (mul_mem (el_mem hg) (el_mem hh)) hu ?_ ?_
  · rw [Equiv.Perm.mul_apply, el_apply hh (by norm_num), el_pt hg (ev_lt hh (by norm_num))]
    exact Nat.eq_of_beq_eq_true m0
  · rw [Equiv.Perm.mul_apply, el_apply hh (by norm_num), el_pt hg (ev_lt hh (by norm_num))]
    exact Nat.eq_of_beq_eq_true m1

end CFSG.KD.HN1408.Cent3

end
