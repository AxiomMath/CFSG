module

public import Certificates.Kernel.LyY.Group

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2Enum CFSG.KC.LyY
open CFSG.Monster.B.Co2 CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.KC.Child3
open CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.Ly1080
open CertificateChecks.KernelLyTr

theorem memN_iff (p : Nat) : ∀ l : List Nat, memN p l = true ↔ p ∈ l
  | [] => by
    change false = true ↔ p ∈ ([] : List Nat)
    simp
  | x :: l => by
    change bIf(Nat.beq x p, true, memN p l) = true ↔ p ∈ x :: l
    rw [List.mem_cons, ← memN_iff p l, Raw.Orb.beq_dec]
    by_cases e : x = p
    · rw [decide_eq_true e]
      exact ⟨fun _ => Or.inl e.symm, fun _ => rfl⟩
    · rw [decide_eq_false e]
      exact ⟨fun h => Or.inr h, fun h => h.resolve_left fun e' => e e'.symm⟩

theorem sumF_succ' (m : Nat) (r : Nat → Nat) : sumF (m + 1) r = sumF m r + r m := by
  change strictN (sumF m r) (fun s' => Nat.add s' (r m)) = _
  rw [strictN_eq']
  rfl

theorem lblCnt_eq (k : Nat) :
    lblCnt 1080 TL k = (Finset.univ.filter fun p : Fin 1080 => lget TL p = k).card := by
  have h : ∀ m, sumF m (fun p => nIf(Nat.beq (lget TL p) k, 1, 0)) =
      ∑ i ∈ Finset.range m, if lget TL i = k then 1 else 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [sumF_succ', ih, Finset.sum_range_succ]
      congr 1
      change nIf(Nat.beq (lget TL m) k, 1, 0) = _
      rw [Raw.Orb.beq_dec]
      by_cases e : lget TL m = k
      · rw [decide_eq_true e, if_pos e]
      · rw [decide_eq_false e, if_neg e]
  unfold lblCnt
  rw [h, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if lget TL i = k then 1 else 0)]

theorem lbl_counts : lblCnt 1080 TL 0 = 648 ∧ lblCnt 1080 TL 1 = 324 ∧ lblCnt 1080 TL 2 = 24 ∧
    lblCnt 1080 TL 3 = 24 ∧ lblCnt 1080 TL 4 = 24 ∧ lblCnt 1080 TL 5 = 24 ∧
    lblCnt 1080 TL 6 = 12 := by
  have h := k_lbl
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h6⟩

theorem lbl_facts (p : Fin 1080) :
    lget TL p < 7 ∧ (lget TL p = 6 ↔ (p : Nat) ∈ lgetL OS 0) := by
  have h := allN_spec c_lbl p p.2
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.blt_eq.mp h1, ?_⟩
  rw [Raw.Orb.beq_dec] at h2
  by_cases e : lget TL p = 6
  · rw [decide_eq_true e] at h2
    exact iff_of_true e ((memN_iff _ _).1 h2)
  · rw [decide_eq_false e] at h2
    have h3 : memN p (lgetL OS 0) = false := by simpa using h2
    exact iff_of_false e fun hm => by
      rw [(memN_iff _ _).2 hm] at h3
      exact Bool.noConfusion h3

theorem lbl_iff (p q : Fin 1080) : lget TL p = lget TL q ↔ ∃ t ∈ Txy0, t p = q := by
  rw [Txy0_eq]
  exact (orbOK_sound prep_gT k_orb p q).symm

theorem lbl_T {t : Perm (Fin 1080)} (ht : t ∈ Txy0) (p : Fin 1080) :
    lget TL (t p) = lget TL p :=
  ((lbl_iff p (t p)).2 ⟨t, ht, rfl⟩).symm

theorem Txy0_le : Txy0 ≤ Y0 := by
  have h := c_sift
  simp only [bAnd_iff] at h
  rw [Txy0_eq, Y0_eq]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, rfl⟩
  exact mem_of_sift (base11.2.2.2.2.1 j j.2).1 (allN_spec h.2.2 j j.2) (prep_gT j)

noncomputable def stabO : Subgroup (Perm (Fin 1080)) where
  carrier := {g | ∀ p : Fin 1080, lget TL (g p) = 6 ↔ lget TL p = 6}
  mul_mem' := fun {a b} ha hb p => by
    rw [Perm.mul_apply, ha, hb]
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {g} hg p => by
    rw [← hg (g⁻¹ p)]
    simp

theorem T_le_stab : Txy0 ≤ stabO := fun t ht p => by rw [lbl_T ht p]

theorem maps_lbl (m : Perm (Fin 1080)) (hm : ∀ t ∈ Txy0, m * t * m⁻¹ ∈ Txy0) (p q : Fin 1080)
    (h : lget TL p = lget TL q) : lget TL (m p) = lget TL (m q) := by
  obtain ⟨t, ht, rfl⟩ := (lbl_iff p q).1 h
  exact (lbl_iff _ _).2 ⟨m * t * m⁻¹, hm t ht, by simp [Perm.mul_apply]⟩

theorem inv_norm (m : Perm (Fin 1080)) (hm : ∀ t ∈ Txy0, m * t * m⁻¹ ∈ Txy0) :
    ∀ t ∈ Txy0, m⁻¹ * t * m⁻¹⁻¹ ∈ Txy0 := by
  intro t ht
  let f : Txy0 → Txy0 := fun s => ⟨m * s * m⁻¹, hm s s.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [f] using this)
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.1 hf) ⟨t, ht⟩
  have e : m * (s : Perm (Fin 1080)) * m⁻¹ = t := congrArg Subtype.val hs
  rw [← e]
  have e2 : m⁻¹ * (m * (s : Perm (Fin 1080)) * m⁻¹) * m⁻¹⁻¹ = s := by group
  rw [e2]
  exact s.2

theorem maps_O (m : Perm (Fin 1080)) (hm : ∀ t ∈ Txy0, m * t * m⁻¹ ∈ Txy0)
    (hm' : ∀ t ∈ Txy0, m⁻¹ * t * m⁻¹⁻¹ ∈ Txy0) (p : Fin 1080) (hp : lget TL p = 6) :
    lget TL (m p) = 6 := by
  have himg : (Finset.univ.filter fun q : Fin 1080 => lget TL q = 6).image m =
      Finset.univ.filter fun q : Fin 1080 => lget TL q = lget TL (m p) := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact maps_lbl m hm r p (hr.trans hp.symm)
    · intro hq
      refine ⟨m⁻¹ q, ?_, by simp⟩
      have := maps_lbl m⁻¹ hm' q (m p) hq
      rw [this]
      simpa using hp
  have hc : lblCnt 1080 TL (lget TL (m p)) = 12 := by
    rw [lblCnt_eq, ← himg, Finset.card_image_of_injective _ m.injective, ← lblCnt_eq]
    exact lbl_counts.2.2.2.2.2.2
  have hlt := (lbl_facts (m p)).1
  obtain ⟨c0, c1, c2, c3, c4, c5, -⟩ := lbl_counts
  generalize lget TL (m p) = l at hc hlt ⊢
  interval_cases l
  · rw [c0] at hc; omega
  · rw [c1] at hc; omega
  · rw [c2] at hc; omega
  · rw [c3] at hc; omega
  · rw [c4] at hc; omega
  · rw [c5] at hc; omega
  · rfl

theorem norm_stab (n : Perm (Fin 1080)) (hn : ∀ t ∈ Txy0, n * t * n⁻¹ ∈ Txy0) : n ∈ stabO := by
  have hn' := inv_norm n hn
  have hn'' : ∀ t ∈ Txy0, n⁻¹⁻¹ * t * n⁻¹⁻¹⁻¹ ∈ Txy0 := by simpa using hn
  intro p
  constructor
  · intro h
    have := maps_O n⁻¹ hn' hn'' (n p) h
    simpa using this
  · exact maps_O n hn hn' p

theorem normalizer_Txy0 (hcard : Nat.card Y0 ≤ 349920) (hT : Nat.card Txy0 = 3888) :
    ∀ n ∈ Y0, (∀ t ∈ Txy0, n * t * n⁻¹ ∈ Txy0) → n ∈ Txy0 := by
  intro n hn hnorm
  let H : Subgroup ↥Y0 := stabO.subgroupOf Y0
  have hTH : Txy0.subgroupOf Y0 ≤ H := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact T_le_stab hx
  obtain ⟨-, h2, h3⟩ := imgOK_sound (prep_S (j := 0) (by norm_num))
    (prep_S (j := 1) (by norm_num)) k_img k_dist
  choose g hg using h2
  have hcl : closure ({permOfArr 1080 yS[0]!, permOfArr 1080 yS[1]!} :
      Set (Perm (Fin 1080))) ≤ Y0 := by
    rw [Y0_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact S_mem (by norm_num)
    · exact S_mem (by norm_num)
  have gY : ∀ i (hi : i < 90), g i hi ∈ Y0 := fun i hi => hcl (hg i hi).1
  have same : ∀ i (hi : i < 90) j (hj : j < 90), (g i hi)⁻¹ * g j hj ∈ stabO →
      ∀ p : Fin 1080, ((p : Nat) ∈ lgetL OS i ↔ (p : Nat) ∈ lgetL OS j) := by
    intro i hi j hj hs p
    rw [(hg i hi).2 p, (hg j hj).2 p, ← (lbl_facts _).2, ← (lbl_facts _).2]
    have := hs ((g j hj)⁻¹ p)
    have e : ((g i hi)⁻¹ * g j hj) ((g j hj)⁻¹ p) = (g i hi)⁻¹ p := by
      simp [Perm.mul_apply]
    rw [e] at this
    exact this
  let F : Fin 90 → ↥Y0 ⧸ H := fun i => QuotientGroup.mk ⟨g i i.2, gY i i.2⟩
  have hF : Function.Injective F := by
    intro i j hij
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hij
    have hs : (g i i.2)⁻¹ * g j j.2 ∈ stabO := hij
    have hsame := same i i.2 j j.2 hs
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · obtain ⟨p, hp⟩ := h3 j j.2 i hlt
      exact hp (hsame p).symm
    · obtain ⟨p, hp⟩ := h3 i i.2 j hlt
      exact hp (hsame p)
  have hidx : 90 ≤ H.index := by
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hmul := Subgroup.card_mul_index H
  have hHc : Nat.card H ≤ 3888 := by nlinarith
  have hTc : Nat.card (Txy0.subgroupOf Y0) = 3888 := by
    rw [← hT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Txy0_le).toEquiv
  have heq := Subgroup.eq_of_le_of_card_ge hTH (by rw [hTc]; exact hHc)
  have hnH : (⟨n, hn⟩ : ↥Y0) ∈ H := by
    rw [Subgroup.mem_subgroupOf]
    exact norm_stab n hnorm
  rw [← heq, Subgroup.mem_subgroupOf] at hnH
  exact hnH

end CertificateChecks.KernelLyY

end
