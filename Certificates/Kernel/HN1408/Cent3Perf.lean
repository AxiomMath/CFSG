module

public import Certificates.Kernel.HN1408.Cent3Card

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

noncomputable abbrev mP : Subgroup (Equiv.Perm (Fin 1408)) :=
  closure {g | g = el (MG 0) ∨ g = el (MG 1)}

theorem mg_lt {l : Nat} (hl : l < 2) : MG l < 1440 := Nat.blt_eq.mp (allN_spec ch441603_mGen l hl)

theorem mElK_parts {E X : Nat → Nat} {n : Nat} (h : mElK E X n = true) :
    E n < 1440 ∧ (n = 0 → E n = 0) ∧ (∀ n' < n, E n ≠ E n') ∧ E n ≠ X 0 ∧ E n ≠ X 1 := by
  unfold mElK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  refine ⟨Nat.blt_eq.mp a, fun h0 => ?_, fun n' hn' e => ?_, bIf_ne_zero' d, bIf_ne_zero' f⟩
  · subst h0
    exact Nat.eq_of_beq_eq_true b
  · have h' := allN_spec c n' hn'
    rw [e] at h'
    simp at h'
where
  bIf_ne_zero' {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : a ≠ b := by
    rintro rfl
    simp at h

theorem e_parts {n : Nat} (hn : n < 60) :
    E n < 1440 ∧ (n = 0 → E n = 0) ∧ (∀ n' < n, E n ≠ E n') ∧ E n ≠ X 0 ∧ E n ≠ X 1 :=
  mElK_parts (allN_spec ch441603_mEl n hn)

theorem e_inj {n n' : Nat} (hn : n < 60) (hn' : n' < 60) (h : E n = E n') : n = n' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (e_parts hn').2.2.1 n hlt h.symm
  · exact (e_parts hn).2.2.1 n' hlt h

variable (hC : Nat.card cC = 1440)
include hC

theorem gen_mP {l : Nat} (hl : l < 2) : el (MG l) ∈ mP := by
  apply Subgroup.subset_closure
  interval_cases l
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem e_mem : ∀ n < 60, el (E n) ∈ mP := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h0 : n = 0
    · rw [(e_parts hn).2.1 h0, el_zero]
      exact one_mem _
    · have h := allN_spec ch441603_mTree n hn
      unfold mTreeK at h
      have e0 : Nat.beq n 0 = false := Bool.eq_false_iff.2 fun h' => h0 (Nat.eq_of_beq_eq_true h')
      rw [e0] at h
      simp only [strictB_app] at h
      obtain ⟨a, h⟩ := mkA h
      obtain ⟨b, c⟩ := mkA h
      have hp := Nat.blt_eq.mp a
      have hl := Nat.blt_eq.mp b
      rw [← el_mul hC (mg_lt hl) (e_parts (by omega)).1 (e_parts hn).1 c]
      exact mul_mem (gen_mP hC hl) (ih _ hp (by omega))

theorem cl_row {n l : Nat} (hn : n < 60) (hl : l < 2) :
    fd (ECl n) l < 60 ∧ el (MG l) * el (E n) = el (E (fd (ECl n) l)) := by
  have h := allN_spec ch441603_mCl n hn
  unfold mClK at h
  simp only [strictB_app] at h
  have h' := allN_spec h l hl
  obtain ⟨a, b⟩ := mkA h'
  have ha := Nat.blt_eq.mp a
  exact ⟨ha, el_mul hC (mg_lt hl) (e_parts hn).1 (e_parts ha).1 b⟩

theorem mem_mP_iff {g : Equiv.Perm (Fin 1408)} : g ∈ mP ↔ ∃ n < 60, g = el (E n) := by
  constructor
  · intro hg
    have hinv : ∀ l < 2, ∀ n < 60, ∃ n' < 60, (el (MG l))⁻¹ * el (E n) = el (E n') := by
      intro l hl n hn
      let σ : Fin 60 → Fin 60 := fun a => ⟨fd (ECl a) l, (cl_row hC a.2 hl).1⟩
      have hσ : Function.Injective σ := by
        intro a b hab
        have e := congrArg Fin.val hab
        have ha := (cl_row hC a.2 hl).2
        have hb := (cl_row hC b.2 hl).2
        have : el (E a) = el (E b) := by
          apply mul_left_cancel (a := el (MG l))
          rw [ha, hb]
          exact congrArg (fun t => el (E t)) e
        exact Fin.ext (e_inj a.2 b.2 (el_inj (e_parts a.2).1 (e_parts b.2).1 this))
      obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hσ) ⟨n, hn⟩
      refine ⟨a, a.2, ?_⟩
      have e : fd (ECl a) l = n := congrArg Fin.val ha
      rw [inv_mul_eq_iff_eq_mul, (cl_row hC a.2 hl).2, e]
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, by norm_num, by rw [(e_parts (by norm_num)).2.1 rfl, el_zero]⟩
    | mul_left x hx y _ ih =>
      obtain ⟨n, hn, rfl⟩ := ih
      rcases hx with rfl | rfl
      · exact ⟨_, (cl_row hC hn (by norm_num : 0 < 2)).1, (cl_row hC hn (by norm_num)).2⟩
      · exact ⟨_, (cl_row hC hn (by norm_num : 1 < 2)).1, (cl_row hC hn (by norm_num)).2⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨n, hn, rfl⟩ := ih
      rcases hx with rfl | rfl
      · exact hinv 0 (by norm_num) n hn
      · exact hinv 1 (by norm_num) n hn
  · rintro ⟨n, hn, rfl⟩
    exact e_mem hC n hn

theorem card_mP : Nat.card mP = 60 := by
  classical
  have hinj : Set.InjOn (fun n => el (E n)) (↑(Finset.range 60) : Set Nat) := by
    intro a ha b hb e
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    exact e_inj ha' hb' (el_inj (e_parts ha').1 (e_parts hb').1 e)
  have hset : (mP : Set (Equiv.Perm (Fin 1408))) =
      (fun n => el (E n)) '' (↑(Finset.range 60) : Set Nat) := by
    ext g
    rw [SetLike.mem_coe, mem_mP_iff hC]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, Finset.mem_range.2 hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, Finset.mem_range.1 hn, rfl⟩
  have hc : Nat.card mP = (mP : Set (Equiv.Perm (Fin 1408))).ncard := Nat.card_coe_set_eq _
  rw [hc, hset, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]

omit hC in
theorem mCommK_parts {E MC MG : Nat → Nat} {l : Nat} (h : mCommK E MC MG l = true) :
    fd (MC l) 0 < 60 ∧ fd (MC l) 1 < 60 ∧
      base2 (fun p => Nat.beq (ev (E (fd (MC l) 0)) (ev (E (fd (MC l) 1)) p))
        (ev (MG l) (ev (E (fd (MC l) 1)) (ev (E (fd (MC l) 0)) p)))) = true := by
  unfold mCommK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, c⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, c⟩

theorem gen_comm {l : Nat} (hl : l < 2) : ∃ e ∈ mP, ∃ f ∈ mP, el (MG l) = e * f * e⁻¹ * f⁻¹ := by
  obtain ⟨ha, hb, hbase⟩ := mCommK_parts (allN_spec ch441603_mComm l hl)
  obtain ⟨b0, b1⟩ := base2_parts hbase
  have ka := (e_parts ha).1
  have kb := (e_parts hb).1
  have km := mg_lt hl
  refine ⟨_, e_mem hC _ ha, _, e_mem hC _ hb, ?_⟩
  have hrel : el (E (fd (MC l) 0)) * el (E (fd (MC l) 1)) =
      el (MG l) * el (E (fd (MC l) 1)) * el (E (fd (MC l) 0)) := by
    refine eq_of_base hC (mul_mem (el_mem ka) (el_mem kb))
      (mul_mem (mul_mem (el_mem km) (el_mem kb)) (el_mem ka)) (Fin.ext ?_) (Fin.ext ?_)
    · simp only [Equiv.Perm.mul_apply]
      rw [el_apply kb (by norm_num), el_pt ka (ev_lt kb (by norm_num)), el_apply ka (by norm_num),
        el_apply kb (ev_lt ka (by norm_num)), el_pt km (ev_lt kb (ev_lt ka (by norm_num)))]
      exact Nat.eq_of_beq_eq_true b0
    · simp only [Equiv.Perm.mul_apply]
      rw [el_apply kb (by norm_num), el_pt ka (ev_lt kb (by norm_num)), el_apply ka (by norm_num),
        el_apply kb (ev_lt ka (by norm_num)), el_pt km (ev_lt kb (ev_lt ka (by norm_num)))]
      exact Nat.eq_of_beq_eq_true b1
  calc el (MG l) = el (MG l) * el (E (fd (MC l) 1)) * el (E (fd (MC l) 0)) *
        (el (E (fd (MC l) 0)))⁻¹ * (el (E (fd (MC l) 1)))⁻¹ := by group
    _ = _ := by rw [← hrel]

theorem comm_mP : ⁅mP, mP⁆ = mP := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  · refine (closure_le _).2 ?_
    rintro g (rfl | rfl)
    · obtain ⟨e, he, f, hf, h⟩ := gen_comm hC (l := 0) (by norm_num)
      rw [h]
      exact commutator_mem_commutator he hf
    · obtain ⟨e, he, f, hf, h⟩ := gen_comm hC (l := 1) (by norm_num)
      rw [h]
      exact commutator_mem_commutator he hf

omit hC in
theorem mP_le : mP ≤ cC := by
  refine (closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact el_mem (mg_lt (by norm_num))
  · exact el_mem (mg_lt (by norm_num))

omit hC in
theorem xK_parts {X : Nat → Nat} (h : xK X = true) :
    X 0 < 1440 ∧ X 1 < 1440 ∧ base2 (fun p => Nat.beq (pt (WK fix3.rep) p) (ev (X 0) p)) = true ∧
      mulEq (X 0) (X 0) (X 1) = true ∧ base2 (fun p => Nat.beq (ev (X 0) (ev (X 1) p)) p) = true := by
  unfold xK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, c, d, f⟩

omit hC in
theorem repP_val : ((repP fix3 : ↥P1408) : Equiv.Perm (Fin 1408)) = elemW fix3.rep := rfl

omit hC in
theorem x_mem (hpf : PrimeFacts 3 [fix3]) :
    ((repP fix3 : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ cC :=
  (mem_cent_iff hpf _).1 (Subgroup.mem_centralizer_singleton_iff.2 rfl)

theorem x_parts (hpf : PrimeFacts 3 [fix3]) :
    ((repP fix3 : ↥P1408) : Equiv.Perm (Fin 1408)) = el (X 0) ∧ el (X 0) * el (X 0) = el (X 1) ∧
      el (X 0) * el (X 1) = 1 := by
  obtain ⟨k0, k1, hb, hm, h3⟩ := xK_parts ch441603_x
  obtain ⟨b0, b1⟩ := base2_parts hb
  obtain ⟨c0, c1⟩ := base2_parts h3
  have hr := repC_word (w := fix3.rep) (by decide)
  refine ⟨eq_el hC (x_mem hpf) k0 ?_ ?_, el_mul hC k0 k0 k1 hm, ?_⟩
  · rw [repP_val, ← repC_pt hr (by norm_num)]
    exact Nat.eq_of_beq_eq_true b0
  · rw [repP_val, ← repC_pt hr (by norm_num)]
    exact Nat.eq_of_beq_eq_true b1
  · rw [← el_zero]
    refine eq_el hC (mul_mem (el_mem k0) (el_mem k1)) (by norm_num) ?_ ?_
    · rw [Equiv.Perm.mul_apply, el_apply k1 (by norm_num), el_pt k0 (ev_lt k1 (by norm_num)),
        ev_zero (by norm_num)]
      exact Nat.eq_of_beq_eq_true c0
    · rw [Equiv.Perm.mul_apply, el_apply k1 (by norm_num), el_pt k0 (ev_lt k1 (by norm_num)),
        ev_zero (by norm_num)]
      exact Nat.eq_of_beq_eq_true c1

omit hC in
theorem perfect60 (hpf : PrimeFacts 3 [fix3]) : Perfect60At (repP fix3) := by
  have hC := hC_of hpf
  obtain ⟨hx, hx2, hx3⟩ := x_parts hC hpf
  let MH : Subgroup ↥P1408 := mP.comap P1408.subtype
  have hmap : MH.map P1408.subtype = mP := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_of_le_right ((mP_le).trans cC_le)
  have hinj : Function.Injective P1408.subtype := P1408.subtype_injective
  refine ⟨MH, fun g hg => (mem_cent_iff hpf g).2 (mP_le hg), ?_, ?_, ?_⟩
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hmap, comm_mP hC]
  · rw [← Subgroup.card_map_of_injective hinj, hmap, card_mP hC]
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgM, hgz⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgz
    have h3 : repP fix3 ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_succ', pow_two, hx, hx2, hx3]
      rfl)
    rw [zpow_eq_zpow_emod' k h3] at hgM ⊢
    have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
    have hM : ∀ m < 2, el (X m) ∉ mP := fun m hm hmem => by
      obtain ⟨n, hn, e⟩ := (mem_mP_iff hC).1 hmem
      have e' := el_inj (by interval_cases m <;> simp_all [xK_parts ch441603_x]) (e_parts hn).1 e
      interval_cases m
      · exact (e_parts hn).2.2.2.1 e'.symm
      · exact (e_parts hn).2.2.2.2 e'.symm
    rcases hk with h | h | h <;> rw [h] at hgM ⊢
    · exact Subgroup.mem_bot.2 (zpow_zero _)
    · exfalso
      have hm : ((repP fix3 ^ (1 : ℤ) : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ mP := hgM
      rw [zpow_one, hx] at hm
      exact hM 0 (by norm_num) hm
    · exfalso
      have hm : ((repP fix3 ^ (2 : ℤ) : ↥P1408) : Equiv.Perm (Fin 1408)) ∈ mP := hgM
      rw [zpow_two, Subgroup.coe_mul, hx, hx2] at hm
      exact hM 1 (by norm_num) hm

end CFSG.KD.HN1408.Cent3

end
