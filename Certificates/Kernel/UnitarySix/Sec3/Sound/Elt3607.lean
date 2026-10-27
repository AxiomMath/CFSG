module

public import Certificates.Kernel.UnitarySix.Sec3.Elt3607
public import Certificates.Kernel.UnitarySix.Sec3.Sound.Glue3601
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.UnitarySix.Sec3.K3607

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem chX3A3_k' : chX3A3.ok = true ∧ chX3A3.order = 8192 :=
  ⟨chX3A3_K.facts'.1, chX3A3_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chSigA3_k' : chSigA3.ok = true ∧ chSigA3.order = 24576 :=
  ⟨chSigA3_K.facts'.1, chSigA3_K.facts'.2.1.trans (by decide +kernel)⟩

theorem lsComm_eq' {Y YI : ℕ} (hY : PermK Y YI = true) :
    (lsGens.all fun g => siftA 693 lvA3 chA3.B 0 (commutatorA 693 (unpack 693 10 Y) g)) =
      !(lsCommK Y YI) := by
  unfold lsCommK lsGens
  rw [Bool.not_not, Array.all_append, chLam_K.O_all, chSig_K.O_all]
  have h1 : chLam.gens.length = 3 := rfl
  have h2 : chSig.gens.length = 2 := rfl
  rw [h1, h2]
  congr 1
  · refine range_all_congr fun j hj => ?_
    have hj' := chLam_P j (h1 ▸ hj)
    rw [commutator_unpack hY hj', lvA3, chA3_K.sift' (canon_comp (canon_comp (PermK.canon hY)
      (PermK.canon hj')) (canon_comp (PermK.canon_inv hY) (PermK.canon_inv hj')))]
    rfl
  · refine range_all_congr fun j hj => ?_
    have hj' := chSig_P j (h2 ▸ hj)
    rw [commutator_unpack hY hj', lvA3, chA3_K.sift' (canon_comp (canon_comp (PermK.canon hY)
      (PermK.canon hj')) (canon_comp (PermK.canon_inv hY) (PermK.canon_inv hj')))]
    rfl

theorem c7_of' {X XI Z ZI : ℕ} {DI : ℕ → ℕ} (hX : PermK X XI = true) (hZ : PermK Z ZI = true)
    (hD : ∀ q < 6, DI q = pinvS 693 10 (mask 10) (dPK q)) (h : c7K X XI Z ZI DI = true) :
    c7At (unpack 693 10 X) (unpack 693 10 Z) = true := by
  have cX := PermK.canon hX
  have cZ := PermK.canon hZ
  unfold c7K at h
  unfold c7At
  refine allLt_iff.2 fun q hq => ?_
  have h1 := allN_spec h q hq
  rw [hD q hq] at h1
  simp only [Bool.or_eq_true] at h1 ⊢
  rcases h1 with ((hl | hs) | ht) | hf
  · left; left
    unfold lsGens
    rw [Array.any_append, Bool.or_eq_true, chLam_K.O_any]
    left
    obtain ⟨j, hj, hw⟩ := List.any_eq_true.1 hl
    have hj' := chLam_P j (List.mem_range.1 hj)
    refine List.any_eq_true.2 ⟨j, hj, ?_⟩
    rw [c7Pt_eq hX hZ hj' hq]
    exact hw
  · left; left
    unfold lsGens
    rw [Array.any_append, Bool.or_eq_true, chSig_K.O_any]
    right
    obtain ⟨j, hj, hw⟩ := List.any_eq_true.1 hs
    have hj' := chSig_P j (List.mem_range.1 hj)
    refine List.any_eq_true.2 ⟨j, hj, ?_⟩
    rw [c7Pt_eq hX hZ hj' hq]
    exact hw
  · left; right
    rw [eq_id cX, eq_id cZ]
    exact ht
  · right
    rw [strictB_eq, strictB_eq, Bool.and_eq_true] at hf
    rw [dArr_unpack hq, comp_unpack cX cZ, comp_unpack (canon_comp cX cZ) (dPK_canon q hq),
      lsComm_eq' hf.1, Bool.not_not]
    exact hf.2

theorem c9_of' {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true) (h : c9K X = true) :
    c9At (unpack 693 10 X) = true := by
  unfold c9K at h
  unfold c9At
  rw [eq_id hX, Bool.or_eq_true]
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [strictB_eq, Bool.and_eq_true] at h
    obtain ⟨hp, hc⟩ := h
    rw [chSig_K.O_all]
    have h2 : chSig.gens.length = 2 := rfl
    rw [h2]
    rw [range_all_congr (n := 2) (g := fun j => sfA3 (pcomp 693 10 (mask 10)
      (pcomp 693 10 (mask 10) X (CSig.S j)) (pcomp 693 10 (mask 10) (pinvS 693 10 (mask 10) X)
        (CSig.SI j)))) fun j hj => by
      have hj' := chSig_P j (h2 ▸ hj)
      rw [commutator_unpack hp hj', lvA3, chA3_K.sift' (canon_comp (canon_comp (PermK.canon hp)
        (PermK.canon hj')) (canon_comp (PermK.canon_inv hp) (PermK.canon_inv hj')))]
      rfl]
    exact hc

theorem i5_of' {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true) :
    i5At (unpack 693 10 X) = i5K X := by
  unfold i5At i5K lvS lvA1
  rw [conjInv_w (by decide) perm_w58.1 hX, chS_K.sift' (conjInv_canon perm_w58.1 hX),
    chA1_K.sift' hX]
  rfl

theorem i8_of' {X Y : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
    (hY : canonK 693 10 (mask 10) (693 * 10) Y = true) :
    i8At (unpack 693 10 X) (unpack 693 10 Y) = i8K X Y := by
  have hP := canon_comp hX hY
  unfold i8At i8K lvS lvA3
  rw [comp_unpack hX hY, conjInv_w (by decide) perm_w58.2 hP,
    chS_K.sift' (conjInv_canon perm_w58.2 hP), chA3_K.sift' hP, strictB_eq]
  rfl

theorem i8b_of' {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true) :
    i8bAt (unpack 693 10 X) = i8bK X := by
  unfold i8bAt i8bK lvX3A3 lvA3
  rw [conjInv_w (w := we) (by decide) perm_we hX, chX3A3_K.sift' (conjInv_canon perm_we hX),
    chA3_K.sift' hX]
  rfl

theorem i5Gen_k' : i5GenCheck = true := by
  unfold i5GenCheck
  rw [Bool.and_eq_true]
  refine ⟨valid_w rfl (by decide) perm_w58.1, ?_⟩
  rw [chA1_K.O_all]
  refine List.all_eq_true.2 fun j hj => ?_
  have hj' := PermK.canon (chA1_P j (List.mem_range.1 hj))
  rw [conjInv_w (by decide) perm_w58.1 hj', lvS, chS_K.sift' (conjInv_canon perm_w58.1 hj')]
  exact List.all_eq_true.1 kI5G j hj

theorem i8Gen_k' : i8GenCheck = true := by
  have hk := kI8G
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk
  unfold i8GenCheck lvX3A3 lvA3
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨valid_w rfl (by decide) perm_w58.2, ?_⟩,
    conj_O_all' chX1_K chX3A3_K chX1_P chX3A3_P h2⟩, conj_O_all' chX3_K chA3_K chX3_P chA3_P h3⟩
  rw [chA3_K.O_all]
  refine List.all_eq_true.2 fun j hj => ?_
  have hj' := PermK.canon (chA3_P j (List.mem_range.1 hj))
  rw [conjInv_w (by decide) perm_w58.2 hj', lvS, chS_K.sift' (conjInv_canon perm_w58.2 hj')]
  exact List.all_eq_true.1 h1 j hj

theorem i8bGen_k' : i8bGenCheck = true := by
  unfold i8bGenCheck
  rw [Bool.and_eq_true]
  refine ⟨valid_w rfl (by decide) perm_we, ?_⟩
  rw [chA3_K.O_all]
  refine List.all_eq_true.2 fun j hj => ?_
  have hj' := PermK.canon (chA3_P j (List.mem_range.1 hj))
  rw [conjInv_w (w := we) (by decide) perm_we hj', lvX3A3,
    chX3A3_K.sift' (conjInv_canon perm_we hj')]
  exact List.all_eq_true.1 kI8bG j hj

theorem nm_k' : nmCheck = true := by
  have hk := kNM
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk
  unfold nmCheck lvZ2S lvA4
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨O_valid chP2_K chP2_P, conj_O_all' chA1_K chZ2S_K chA1_P chZ2S_P h1⟩,
    conj_O_all' chA1_K chA4_K chA1_P chA4_P h2⟩, conj_O_all' chP2_K chA4_K chP2_P chA4_P h3⟩

section

open CFSG.Monster.B.Co2

theorem c11a_k' : ∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ c11aAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chZ2S_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide)
      kH3607_parts.1 x hx
  exact ⟨_, hR, (c11a_L hL).trans hf⟩

theorem c6_k' : ∀ x ∈ chLam.grp, ∃ a, Rep 693 a x ∧ c6At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chLam_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide)
      kH3607_parts.2.1 x hx
  exact ⟨_, hR, (c6_L hL).trans hf⟩

theorem c9_k' : ∀ x ∈ chSig.grp, ∃ a, Rep 693 a x ∧ c9At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chSig_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide)
      kH3607_parts.2.2.1 x hx
  rw [strictB_eq] at hf
  exact ⟨_, hR, c9_of' (prodL_canon hL) hf⟩

theorem i5_k' : ∀ x ∈ chT1.grp, ∃ a, Rep 693 a x ∧ i5At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chT1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide)
      kH3607_parts.2.2.2.1 x hx
  rw [strictB_eq] at hf
  exact ⟨_, hR, (i5_of' (prodL_canon hL)).trans hf⟩

theorem i8_k' : ∀ x ∈ chX1.grp, ∀ y ∈ chX3.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧
    i8At a b = true := by
  intro x hx y hy
  obtain ⟨L, hL, hR, hf⟩ :=
    chX1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide)
      kH3607_parts.2.2.2.2.1 x hx
  obtain ⟨L', hL', hR', hf'⟩ :=
    chX3_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hf y hy
  rw [strictB_eq, strictB_eq] at hf'
  exact ⟨_, _, hR, hR', (i8_of' (prodL_canon hL) (prodL_canon hL')).trans hf'⟩

theorem i8b_k' : ∀ x ∈ chX3.grp, ∃ a, Rep 693 a x ∧ i8bAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chX3_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide)
      kH3607_parts.2.2.2.2.2 x hx
  rw [strictB_eq] at hf
  exact ⟨_, hR, (i8b_of' (prodL_canon hL)).trans hf⟩

theorem c7_k' : ∀ x ∈ chLam.grp, ∀ y ∈ chSig.grp, ∃ a b, Rep 693 a x ∧ Rep 693 b y ∧
    c7At a b = true := by
  have hk : prodLazyK 693 (693 * 10) CLam.LR CLam.TR c7SD 3 0 [] = true := by
    refine c7_all fun a ha b hb => ?_
    interval_cases a <;> interval_cases b
    exacts [kC7_0_0, kC7_0_1, kC7_0_2, kC7_0_3, kC7_1_0, kC7_1_1, kC7_1_2, kC7_1_3, kC7_2_0,
      kC7_2_1, kC7_2_2, kC7_2_3, kC7_3_0, kC7_3_1, kC7_3_2, kC7_3_3, kC7_4_0, kC7_4_1, kC7_4_2,
      kC7_4_3]
  intro x hx y hy
  obtain ⟨L, -, hR, hf⟩ :=
    chLam_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hk x hx
  unfold c7SD c7S at hf
  rw [strictB_eq, strictB_eq, Bool.and_eq_true] at hf
  obtain ⟨L', -, hR', hf'⟩ :=
    chSig_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hf.2 y hy
  rw [strictB_eq, strictB_eq, Bool.and_eq_true] at hf'
  exact ⟨_, _, hR, hR', c7_of' hf.1 hf'.1 dselK_eq hf'.2⟩

end

end CertificateChecks.KernelU6.Sec3
