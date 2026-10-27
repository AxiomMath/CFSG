module

public import Certificates.Kernel.HN1408.ClsZ1Facts
public import Certificates.Kernel.HN1408.W441875Chk
public import Certificates.Kernel.HN1408.W441875Rows

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441875

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev cK : Subgroup (Equiv.Perm (Fin 1408)) := Tr2.genC classz₁.centGens

noncomputable abbrev vH : Fin 5 → ↥P1408 := ![pA, pZ, pA * pZ, pB, pZ₁]

@[expose] noncomputable def el (k : Nat) : Equiv.Perm (Fin 1408) :=
  Tr2.t0P Cz1T.cz1T_ok (k / 24) * Tr2.t1P Cz1T.cz1T_ok (k % 24)

theorem el_mem {k : Nat} (hk : k < 3840) : el k ∈ cK :=
  mul_mem (Tr2.t0P_spec Cz1T.cz1T_ok (by omega)).1
    (Tr2.t1P_spec Cz1T.cz1T_ok (Nat.mod_lt _ (by norm_num))).1

theorem repC_el {k : Nat} (hk : k < 3840) : RepC (elK k) (el k) := by
  have e : elK k = pc (Cz1T.T0 (k / 24)) (Cz1T.T1 (k % 24)) := rfl
  rw [e]
  exact repC_pc (Tr2.t0P_spec Cz1T.cz1T_ok (i := k / 24) (by omega)).2
    (Tr2.t1P_spec Cz1T.cz1T_ok (j := k % 24) (Nat.mod_lt _ (by norm_num))).2

theorem el_pt {k p : Nat} (hk : k < 3840) (hp : p < 1408) : (el k ⟨p, hp⟩).val = ev k p := by
  have h1 := repC_pt (Tr2.t1P_spec Cz1T.cz1T_ok (j := k % 24) (Nat.mod_lt _ (by norm_num))).2 hp
  have h2 := repC_pt (Tr2.t0P_spec Cz1T.cz1T_ok (i := k / 24) (by omega)).2
    (Fin.isLt (Tr2.t1P Cz1T.cz1T_ok (k % 24) ⟨p, hp⟩))
  have e : ev k p = pt (Cz1T.T0 (k / 24)) (pt (Cz1T.T1 (k % 24)) p) := rfl
  rw [e, h1, h2, el, Equiv.Perm.mul_apply]

theorem ev_lt {k p : Nat} (hk : k < 3840) (hp : p < 1408) : ev k p < 1408 := by
  rw [← el_pt hk hp]
  exact Fin.isLt _

theorem el_apply {k p : Nat} (hk : k < 3840) (hp : p < 1408) :
    el k ⟨p, hp⟩ = ⟨ev k p, ev_lt hk hp⟩ :=
  Fin.ext (el_pt hk hp)

theorem el_inj {k k' : Nat} (hk : k < 3840) (hk' : k' < 3840) (h : el k = el k') : k = k' := by
  obtain ⟨h1, h2⟩ := Tr2.el_inj Cz1T.cz1T_ok (i := k / 24) (i' := k' / 24) (j := k % 24)
    (j' := k' % 24) (by omega) (by omega) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) h
  omega

theorem el_zero : el 0 = 1 := by
  have h0 := Tr2.headK_parts Cz1T.cz1T_ok.head
  have e1 : Tr2.t0P Cz1T.cz1T_ok 0 = 1 :=
    eq_of_repC (Tr2.t0P_spec Cz1T.cz1T_ok (by norm_num)).2 (by rw [h0.2.2.1]; exact Tr2.repC_idK)
  have e2 : Tr2.t1P Cz1T.cz1T_ok 0 = 1 :=
    eq_of_repC (Tr2.t1P_spec Cz1T.cz1T_ok (by norm_num)).2 (by rw [h0.2.2.2]; exact Tr2.repC_idK)
  rw [el, Nat.zero_div, Nat.zero_mod, e1, e2, one_mul]

theorem ev_zero {p : Nat} (hp : p < 1408) : ev 0 p = p := by
  rw [← el_pt (k := 0) (by norm_num) hp, el_zero]
  rfl

theorem base2_parts {f : Nat → Bool} (h : base2 f = true) : f 0 = true ∧ f 1 = true := mkA h

theorem bAnd_true {a b : Bool} (ha : a = true) (hb : b = true) : bAnd(a, b) = true := by
  rw [ha]
  exact hb

theorem bIf_ne_zero {k : Nat} (h : bIf(Nat.beq k 0, false, true) = true) : k ≠ 0 := by
  rintro rfl
  exact absurd h (by decide)

theorem bIf_of_ne_zero {k : Nat} (h : k ≠ 0) : bIf(Nat.beq k 0, false, true) = true := by
  have e : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
  rw [e]

theorem sq_pt {k p : Nat} (hk : k < 3840) (hp : p < 1408) :
    ((el k * el k) ⟨p, hp⟩).val = ev k (ev k p) := by
  rw [Equiv.Perm.mul_apply, el_apply hk hp, el_pt hk (ev_lt hk hp)]

theorem repK_parts {c : Nat} (h : repK RK RT RW c = true) : RK c < 3840 ∧ RT c < 5 ∧
    lettersOK (RW.getD c []) = true ∧
      pc (WK (RW.getD c [])) (tgtK (RT c)) = pc (elK (RK c)) (WK (RW.getD c [])) := by
  unfold repK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, d⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, c, Nat.eq_of_beq_eq_true d⟩

section Card

variable (hK : Nat.card cK = 3840)
include hK

theorem exists_el {g : Equiv.Perm (Fin 1408)} (hg : g ∈ cK) : ∃ k < 3840, g = el k := by
  classical
  let E : Finset (Equiv.Perm (Fin 1408)) := (Finset.range 3840).image el
  have hinj : Set.InjOn el ↑(Finset.range 3840) := fun k hk k' hk' e =>
    el_inj (Finset.mem_range.1 hk) (Finset.mem_range.1 hk') e
  have hE : E.card = 3840 := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (↑E : Set (Equiv.Perm (Fin 1408))) ⊆ (cK : Set (Equiv.Perm (Fin 1408))) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact el_mem (Finset.mem_range.1 hk)
  have hc : (cK : Set (Equiv.Perm (Fin 1408))).ncard = 3840 := by
    rw [← Nat.card_coe_set_eq]
    exact hK
  have heq : (↑E : Set (Equiv.Perm (Fin 1408))) = (cK : Set (Equiv.Perm (Fin 1408))) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc, Set.ncard_coe_finset, hE]) (Set.toFinite _)
  have hg' : g ∈ (↑E : Set (Equiv.Perm (Fin 1408))) := by
    rw [heq]
    exact hg
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hg'
  exact ⟨k, Finset.mem_range.1 hk, rfl⟩

theorem eq_of_base {g h : Equiv.Perm (Fin 1408)} (hg : g ∈ cK) (hh : h ∈ cK)
    (h0 : g ⟨0, by norm_num⟩ = h ⟨0, by norm_num⟩)
    (h1 : g ⟨1, by norm_num⟩ = h ⟨1, by norm_num⟩) : g = h := by
  obtain ⟨k, hk, rfl⟩ := exists_el hK hg
  obtain ⟨k', hk', rfl⟩ := exists_el hK hh
  have hj : k % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hj' : k' % 24 < 24 := Nat.mod_lt _ (by norm_num)
  simp only [el, Equiv.Perm.mul_apply, Tr2.t1P_zero Cz1T.cz1T_ok hj,
    Tr2.t1P_zero Cz1T.cz1T_ok hj'] at h0
  have ei := Tr2.t0P_inj Cz1T.cz1T_ok (by omega) (by omega) h0
  simp only [el, Equiv.Perm.mul_apply] at h1
  rw [ei] at h1
  have ej := Tr2.t1P_inj Cz1T.cz1T_ok hj hj' ((Tr2.t0P Cz1T.cz1T_ok (k' / 24)).injective h1)
  have e : k = k' := by omega
  rw [e]

theorem eq_el {g : Equiv.Perm (Fin 1408)} (hg : g ∈ cK) {k : Nat} (hk : k < 3840)
    (h0 : (g ⟨0, by norm_num⟩).val = ev k 0) (h1 : (g ⟨1, by norm_num⟩).val = ev k 1) :
    g = el k :=
  eq_of_base hK hg (el_mem hk) (Fin.ext (by rw [h0, el_pt hk])) (Fin.ext (by rw [h1, el_pt hk]))

theorem invK_iff {k : Nat} (hk : k < 3840) : invK k = true ↔ el k * el k = 1 ∧ el k ≠ 1 := by
  constructor
  · intro h
    unfold invK at h
    obtain ⟨h1, h2⟩ := mkA h
    obtain ⟨b0, b1⟩ := base2_parts h2
    refine ⟨?_, fun e => bIf_ne_zero h1 (el_inj hk (by norm_num) (e.trans el_zero.symm))⟩
    rw [← el_zero]
    refine eq_el hK (mul_mem (el_mem hk) (el_mem hk)) (by norm_num) ?_ ?_
    · rw [sq_pt hk, ev_zero (by norm_num)]
      exact Nat.eq_of_beq_eq_true b0
    · rw [sq_pt hk, ev_zero (by norm_num)]
      exact Nat.eq_of_beq_eq_true b1
  · rintro ⟨h2, h1⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h1 el_zero
    have hp : ∀ p (hp : p < 1408), ev k (ev k p) = p := fun p hp => by
      rw [← sq_pt hk hp, h2]
      rfl
    unfold invK
    have e0 := hp 0 (by norm_num)
    have e1 := hp 1 (by norm_num)
    refine bAnd_true (bIf_of_ne_zero hk0) (bAnd_true ?_ ?_)
    · simp only [e0, Nat.beq_refl]
    · simp only [e1, Nat.beq_refl]

theorem row_zero {k : Nat} (hk : k < 3840) (h0 : R k = 0) : ¬ (el k * el k = 1 ∧ el k ≠ 1) := by
  intro hi
  have h := allN_spec ch441875_rows k hk
  unfold rowK at h
  simp only [strictB_app] at h
  rw [h0, (invK_iff hK hk).2 hi] at h
  exact Bool.false_ne_true h

theorem row_conj {k : Nat} (hk : k < 3840) (h0 : R k ≠ 0) :
    (R k - 1) % 16 < 15 ∧ ∃ c' < 3840, el c' * el (RK ((R k - 1) % 16)) = el k * el c' := by
  have h := allN_spec ch441875_rows k hk
  unfold rowK at h
  have e0 : Nat.beq (R k) 0 = false := Bool.eq_false_iff.2 fun h' => h0 (Nat.eq_of_beq_eq_true h')
  simp only [strictB_app] at h
  rw [e0] at h
  obtain ⟨-, h⟩ := mkA h
  obtain ⟨hc, h⟩ := mkA h
  obtain ⟨hc', h⟩ := mkA h
  obtain ⟨b0, b1⟩ := base2_parts h
  have hc15 : (R k - 1) % 16 < 15 := Nat.blt_eq.mp hc
  have hc1 : (R k - 1) / 16 < 3840 := Nat.blt_eq.mp hc'
  refine ⟨hc15, _, hc1, ?_⟩
  have hrk : RK ((R k - 1) % 16) < 3840 := (repK_parts (allN_spec ch441875_rep _ hc15)).1
  refine eq_of_base hK (mul_mem (el_mem hc1) (el_mem hrk)) (mul_mem (el_mem hk) (el_mem hc1))
    (Fin.ext ?_) (Fin.ext ?_)
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, el_apply hrk (by norm_num),
      el_pt hc1 (ev_lt hrk (by norm_num)), el_apply hc1 (by norm_num),
      el_pt hk (ev_lt hc1 (by norm_num))]
    exact Nat.eq_of_beq_eq_true b0
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, el_apply hrk (by norm_num),
      el_pt hc1 (ev_lt hrk (by norm_num)), el_apply hc1 (by norm_num),
      el_pt hk (ev_lt hc1 (by norm_num))]
    exact Nat.eq_of_beq_eq_true b1

end Card

theorem cK_le : cK ≤ P1408 := by
  refine (closure_le _).2 ?_
  rintro _ ⟨w, -, rfl⟩
  exact elemW_mem w

@[expose] noncomputable def elH {k : Nat} (hk : k < 3840) : ↥P1408 := ⟨el k, cK_le (el_mem hk)⟩

theorem elH_val {k : Nat} (hk : k < 3840) : ((elH hk : ↥P1408) : Equiv.Perm (Fin 1408)) = el k :=
  rfl

theorem repC_tgt {t : Nat} (ht : t < 5) :
    RepC (tgtK t) ((vH ⟨t, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) := by
  interval_cases t
  · have e1 : tgtK 0 = WK wordA := rfl
    have e2 : ((vH ⟨0, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordA := rfl
    rw [e1, e2]
    exact repC_word (by decide)
  · have e1 : tgtK 1 = WK wordZ := rfl
    have e2 : ((vH ⟨1, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordZ := rfl
    rw [e1, e2]
    exact repC_word (by decide)
  · have e1 : tgtK 2 = pc (WK wordA) (WK wordZ) := rfl
    have e2 : ((vH ⟨2, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordA * elemW wordZ := rfl
    rw [e1, e2]
    exact repC_pc (repC_word (by decide)) (repC_word (by decide))
  · have e1 : tgtK 3 = WK wordB := rfl
    have e2 : ((vH ⟨3, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordB := rfl
    rw [e1, e2]
    exact repC_word (by decide)
  · have e1 : tgtK 4 = WK wordZ₁ := rfl
    have e2 : ((vH ⟨4, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW wordZ₁ := rfl
    rw [e1, e2]
    exact repC_word (by decide)

theorem rep_conj {c : Nat} (hc : c < 15) :
    ∃ (hk : RK c < 3840) (ht : RT c < 5), IsConj (vH ⟨RT c, ht⟩) (elH hk) := by
  obtain ⟨hk, ht, hl, he⟩ := repK_parts (allN_spec ch441875_rep c hc)
  refine ⟨hk, ht, isConj_iff.2 ⟨⟨elemW (RW.getD c []), elemW_mem _⟩, Subtype.ext ?_⟩⟩
  have h1 := repC_pc (repC_word hl) (repC_tgt ht)
  have h2 := repC_pc (repC_el hk) (repC_word hl)
  rw [he] at h1
  have e := eq_of_repC h1 h2
  change elemW (RW.getD c []) * ((vH ⟨RT c, ht⟩ : ↥P1408) : Equiv.Perm (Fin 1408)) *
    (elemW (RW.getD c []))⁻¹ = el (RK c)
  rw [e, mul_inv_cancel_right]

theorem vH_inv (t : Fin 5) : ((vH t : ↥P1408) : Equiv.Perm (Fin 1408)) *
    (vH t : ↥P1408) = 1 ∧ ((vH t : ↥P1408) : Equiv.Perm (Fin 1408)) ≠ 1 := by
  have h := allN_spec ch441875_tgt t.val t.isLt
  unfold tgtInvK invX at h
  simp only [strictB_app] at h
  obtain ⟨h1, h2⟩ := mkA h
  have hr := repC_tgt t.isLt
  have e : (⟨t.val, t.isLt⟩ : Fin 5) = t := rfl
  rw [e] at hr
  refine ⟨eq_of_repC (repC_pc hr hr) ?_, fun e1 => ?_⟩
  · rw [Nat.eq_of_beq_eq_true h1]
    exact Tr2.repC_idK
  · have hp : pt (tgtK t) 0 = 0 := by
      rw [repC_pt hr (by norm_num : 0 < 1408), e1]
      rfl
    rw [hp] at h2
    exact absurd h2 (by decide)

end CFSG.KD.HN1408.W441875

end
