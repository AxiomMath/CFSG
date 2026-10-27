module

public import Certificates.Kernel.UnitarySix.Sec3.F3601
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6

section

variable {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
include hX

theorem zS_of' : zSAt (unpack 693 10 X) = zSK X := by
  unfold zSAt zSK lvZ
  rw [O_all_comm chS_K chS_P' hX, chZ_K.sift' hX]
  rfl

theorem a1_of' : a1At (unpack 693 10 X) = a1K (wK we) X := by
  unfold a1At a1K lvZ lvX1Z lvA2 ae
  rw [O_all_comm chA1_K chA1_P hX, (wK_spec (w := we) (by decide)).1,
    commA_unpack hX (PermK.canon perm_we), O_all_comm chX6Z_K chX6Z_P hX, chZ_K.sift' hX,
    chX1Z_K.sift' hX, chA2_K.sift' hX]
  rfl

theorem a2_of' : a2At (unpack 693 10 X) = a2K X := by
  unfold a2At a2K lvA1 lvX6Z
  rw [chA1_K.sift' hX, chX6Z_K.sift' hX]
  rfl

theorem z2s_of' : z2sAt (unpack 693 10 X) =
    z2sK (sec3G 16) (pinvS 693 10 (mask 10) (sec3G 16)) (wK wg232) (wKI wg232) X := by
  have h16 := kGP 16 (by norm_num)
  unfold z2sAt z2sK lvZ2S lvZ ag232
  rw [hG 16 (by norm_num), conj_unpack h16 hX, (wK_spec (w := wg232) (by decide)).1,
    conj_unpack perm_wg232 hX, chZ2S_K.sift' (conj_canon hX h16),
    chZ2S_K.sift' (conj_canon hX perm_wg232), chZ_K.sift' hX]
  rfl

end

section

variable {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
include hL

theorem zA3_L' : zA3At (unpack 693 10 (prodL 693 10 (mask 10) L)) = zA3L (wK we) L := by
  have hX := prodL_canon hL
  have hE := PermK.canon perm_we
  unfold zA3At zA3L lvA4 ae
  rw [chA3_K.O_any, range_any_congr fun j hj => commFail_unpack hL (PermK.canon (chA3_P j hj)),
    O_all_comm chA3_K chA3_P hX, chA4_K.sift' hX, (wK_spec (w := we) (by decide)).1,
    commFail_unpack hL hE, commA_unpack hX hE, strictB_eq, strictB_eq]
  rfl

omit hL in
theorem p2Kof' {X : ℕ} (h : p2K X = true) :
    (!(chA3.O.all fun s => siftA 693 lvA3 chA3.B 0 (conjA 693 (unpack 693 10 X) s)) ||
      siftA 693 lvP2 chP2.B 0 (unpack 693 10 X)) = true := by
  unfold p2K at h
  rw [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨hp, h⟩ := h
  have hX := PermK.canon hp
  unfold lvA3 lvP2
  rw [chA3_K.O_all, chP2_K.sift' hX,
    range_all_congr fun j hj => by
      rw [conj_unpack hp (PermK.canon (chA3_P j hj)),
        chA3_K.sift' (canon_comp hX (canon_comp (PermK.canon (chA3_P j hj)) (PermK.canon_inv hp)))]]
  exact h

theorem p2_L' (h : p2L L = true) : p2At (unpack 693 10 (prodL 693 10 (mask 10) L)) = true := by
  have hX := prodL_canon hL
  unfold p2L at h
  unfold p2At
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have h' : ((List.range chA3.gens.length).all fun j => pg 10 (mask 10) sec3LabA3
        (ptL 10 (mask 10) L (pg 10 (mask 10) (CA3.S j) 2)) == pg 10 (mask 10) sec3LabA3
        (ptL 10 (mask 10) L 2)) = false := by simpa using h
    have hA : (chA3.O.all fun s => labA3[(unpack 693 10 (prodL 693 10 (mask 10) L))[s[2]!]!]! ==
        labA3[(unpack 693 10 (prodL 693 10 (mask 10) L))[2]!]!) = false := by
      rw [chA3_K.O_all, range_all_congr fun j hj => by
        have hj' := PermK.canon (chA3_P j hj)
        have h2 : pg 10 (mask 10) (CA3.S j) 2 < 693 := canon_lt hj' (by norm_num)
        rw [unpack_get (by norm_num : 2 < 693), prodL_get hL h2, prodL_get hL (by norm_num),
          labA3_eq _ (ptL_lt hL h2), labA3_eq _ (ptL_lt hL (by norm_num))]]
      exact h'
    rw [hA]
    rfl
  · rw [Bool.or_assoc, p2Kof' h, Bool.or_true]

end

theorem a4_of' {J J2 X : ℕ} (hJ : J = wK wj₀) (hJ2 : J2 = wK wj₀sq)
    (h : a4K J (wKI wj₀) J2 (wKI wj₀sq) X = true) : a4At (unpack 693 10 X) = true := by
  subst hJ hJ2
  unfold a4K at h
  rw [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨hp, h⟩ := h
  have hX := PermK.canon hp
  unfold a4At lvZ lvA1 lvZ2S lvX8 aj₀ aj₀sq
  rw [O_all_comm chX1_K chX1_P hX, chZ_K.sift' hX, chA1_K.sift' hX, chZ2S_K.sift' hX,
    (wK_spec (w := wj₀) (by decide)).1, (wK_spec (w := wj₀sq) (by decide)).1,
    commutator_unpack hp perm_wj₀, commutator_unpack hp perm_wj₀sq,
    chX8_K.sift' (canon_comp (canon_comp hX (PermK.canon perm_wj₀))
      (canon_comp (PermK.canon_inv hp) (PermK.canon_inv perm_wj₀))),
    chX8_K.sift' (canon_comp (canon_comp hX (PermK.canon perm_wj₀sq))
      (canon_comp (PermK.canon_inv hp) (PermK.canon_inv perm_wj₀sq)))]
  exact h

theorem a4Pair_of' {Y X : ℕ} (h : a4PairK Y X = true) :
    a4PairAt (unpack 693 10 Y) (unpack 693 10 X) = true := by
  unfold a4PairK at h
  rw [strictB_eq, strictB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hy, hx⟩, h⟩ := h
  have hY := PermK.canon hy
  have hX := PermK.canon hx
  unfold a4PairAt lvZ lvZ2S
  rw [eq_id hY, commutator_unpack hy hx, chZ_K.sift' (canon_comp (canon_comp hY hX)
    (canon_comp (PermK.canon_inv hy) (PermK.canon_inv hx))), chZ2S_K.sift' hX]
  exact h

theorem z2sPair_of' {Y X : ℕ} (h : z2sPairK Y X = true) :
    z2sPairAt (unpack 693 10 Y) (unpack 693 10 X) = true := by
  unfold z2sPairK at h
  rw [strictB_eq, strictB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hy, hx⟩, h⟩ := h
  have hY := PermK.canon hy
  have hX := PermK.canon hx
  unfold z2sPairAt lvZ
  rw [commutator_unpack hy hx, chZ_K.sift' (canon_comp (canon_comp hY hX)
    (canon_comp (PermK.canon_inv hy) (PermK.canon_inv hx)))]
  exact h

theorem a1Gen_k' : a1GenCheck = true := by
  have hk := kA1G
  rw [Bool.and_eq_true] at hk
  unfold a1GenCheck lvZ
  rw [Bool.and_eq_true, chA1_K.O_all, chA1_K.O_all]
  refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun j hj => ?_⟩
  · have hj' := PermK.canon (chA1_P j (List.mem_range.1 hj))
    rw [comp_unpack hj' hj', chZ_K.sift' (canon_comp hj' hj')]
    exact List.all_eq_true.1 hk.1 j hj
  · rw [chA1_K.O_all]
    refine List.all_eq_true.2 fun i hi => ?_
    have hj' := chA1_P j (List.mem_range.1 hj)
    have hi' := chA1_P i (List.mem_range.1 hi)
    rw [commutator_unpack hj' hi', chZ_K.sift' (canon_comp (canon_comp (PermK.canon hj')
      (PermK.canon hi')) (canon_comp (PermK.canon_inv hj') (PermK.canon_inv hi')))]
    exact List.all_eq_true.1 (List.all_eq_true.1 hk.2 j hj) i hi

theorem uA_k' : uACheck = true := by
  unfold uACheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨valid_w (w := we) rfl (by decide) perm_we,
    valid_w (w := wj₀sq) rfl (by decide) perm_wj₀sq⟩,
    valid_w (w := wg232) rfl (by decide) perm_wg232⟩, O_valid chLam_K chLam_P⟩,
    O_valid chSig_K chSig_P⟩, O_valid chA1_K chA1_P⟩, O_valid chX1_K chX1_P⟩, ?_⟩
  unfold nativeA
  rw [List.all_map]
  refine List.all_eq_true.2 fun w hw => ?_
  have hk := List.all_eq_true.1 kUA w hw
  rw [strictB_eq, Bool.and_eq_true] at hk
  have hr : ∀ c ∈ w, c.natAbs - 1 < 46 := by
    have h : ∀ w ∈ CFSG.EvenSmallLie.UnitarySix.aWords, ∀ c ∈ w, c.natAbs - 1 < 46 := by
      decide +kernel
    exact h w hw
  obtain ⟨e, hc⟩ := natK_spec w hr
  simp only [Function.comp_apply]
  rw [e, Bool.and_eq_true, PermK.valid hk.1]
  unfold lvA2
  rw [chA2_K.sift' hc]
  exact ⟨rfl, hk.2⟩

end CertificateChecks.KernelU6.Sec3
