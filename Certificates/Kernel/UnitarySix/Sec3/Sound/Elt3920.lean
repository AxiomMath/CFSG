module

public import Certificates.Kernel.UnitarySix.Sec3.Elt3920
public import Certificates.Kernel.UnitarySix.Sec3.K3920G
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.EvenSmallLie.UnitarySix.YamadaHAut
open CFSG.RankThree.Native

theorem p4Kof' {X : ℕ} (h : p4K X = true) :
    (!(chA4.O.all fun s => siftA 693 lvA4 chA4.B 0 (conjA 693 (unpack 693 10 X) s)) ||
      siftA 693 lvP2 chP2.B 0 (unpack 693 10 X)) = true := by
  unfold p4K at h
  rw [strictB_eq, Bool.and_eq_true] at h
  obtain ⟨hp, h⟩ := h
  have hX := PermK.canon hp
  have hl : chA4.gens.length = 4 := rfl
  unfold lvA4 lvP2
  rw [chA4_K.O_all, chP2_K.sift' hX, hl,
    range_all_congr fun j hj => by
      rw [conj_unpack hp (PermK.canon (chA4_P j (hl ▸ hj))),
        chA4_K.sift' (canon_comp hX (canon_comp (PermK.canon (chA4_P j (hl ▸ hj)))
          (PermK.canon_inv hp)))]]
  exact h

theorem p4_L' {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
    (h : p4L L = true) : p4At (unpack 693 10 (prodL 693 10 (mask 10) L)) = true := by
  unfold p4L at h
  unfold p4At
  have hl : chA4.gens.length = 4 := rfl
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have h' : ((List.range 4).all fun j => pg 10 (mask 10) sec3LabA4
        (ptL 10 (mask 10) L (pg 10 (mask 10) (CA4.S j) 1)) == pg 10 (mask 10) sec3LabA4
        (ptL 10 (mask 10) L 1)) = false := by simpa using h
    have hA : (chA4.O.all fun s => labA4[(unpack 693 10 (prodL 693 10 (mask 10) L))[s[1]!]!]! ==
        labA4[(unpack 693 10 (prodL 693 10 (mask 10) L))[1]!]!) = false := by
      rw [chA4_K.O_all, hl, range_all_congr fun j hj => by
        have hj' := PermK.canon (chA4_P j (hl ▸ hj))
        have h2 : pg 10 (mask 10) (CA4.S j) 1 < 693 := canon_lt hj' (by norm_num)
        rw [unpack_get (by norm_num : 1 < 693), prodL_get hL h2, prodL_get hL (by norm_num),
          labA4_eq _ (ptL_lt hL h2), labA4_eq _ (ptL_lt hL (by norm_num))]]
      exact h'
    rw [hA]
    rfl
  · rw [Bool.or_assoc, p4Kof' h, Bool.or_true]

theorem outer_k' : outerCheck = true := by
  unfold outerCheck
  have e : ∀ q < 5, dArr[q + 1]! = unpack 693 10 (dPK (q + 1)) := fun q hq =>
    dArr_unpack (by omega)
  have l : [dTab, d2Tab, sTab, dsTab, d2sTab] = (List.range 5).map fun q => dArr[q + 1]! := rfl
  rw [l, List.all_map]
  refine List.all_eq_true.2 fun q hq => ?_
  have hq' := List.mem_range.1 hq
  rw [Function.comp_apply, e q hq', lvL, chL_K.sift' (dPK_canon _ (by omega))]
  exact List.all_eq_true.1 kOuter q hq

theorem pconj_O_all' {d : ChainData} {kS' nb' BP' NS' : ℕ} {PS' PSI' LR' TR' TRI' : ℕ → ℕ}
    (hd : ChainK d kS' nb' BP' NS' PS' PSI' LR' TR' TRI')
    (hQ : ∀ i < d.gens.length, PermK (PS' i) (PSI' i) = true) {D DI : ℕ} (hp : PermK D DI = true)
    (hk : ((List.range d.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR' TRI' BP' nb' 0
        (pcomp 693 10 (mask 10) D (pcomp 693 10 (mask 10) (PS' i) DI))) = true) :
    (d.O.all fun a => siftA 693 d.levels d.B 0 (conjA 693 (unpack 693 10 D) a)) = true := by
  rw [hd.O_all]
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' := PermK.canon (hQ i (List.mem_range.1 hi))
  rw [conj_unpack hp hi', hd.sift' (conj_canon hi' hp)]
  exact List.all_eq_true.1 hk i hi

theorem normBy_of' {d : ChainData} {kS' nb' BP' NS' : ℕ} {PS' PSI' LR' TR' TRI' : ℕ → ℕ}
    (hd : ChainK d kS' nb' BP' NS' PS' PSI' LR' TR' TRI')
    (hQ : ∀ i < d.gens.length, PermK (PS' i) (PSI' i) = true)
    (hk : ((List.range d.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR' TRI' BP' nb' 0
        (pcomp 693 10 (mask 10) (dPK 1) (pcomp 693 10 (mask 10) (PS' i)
          (pinvS 693 10 (mask 10) (dPK 1)))) &&
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) LR' TRI' BP' nb' 0
        (pcomp 693 10 (mask 10) (dPK 3) (pcomp 693 10 (mask 10) (PS' i)
          (pinvS 693 10 (mask 10) (dPK 3))))) = true) :
    normBy d d.levels = true := by
  unfold normBy
  rw [Array.all_eq_true]
  intro j hj
  have h1 := pconj_O_all' hd hQ (dPK_perm 1 (by norm_num)) (List.all_eq_true.2 fun i hi =>
    (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hk i hi).1)
  have h2 := pconj_O_all' hd hQ (dPK_perm 3 (by norm_num)) (List.all_eq_true.2 fun i hi =>
    (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hk i hi).2)
  rw [Array.all_eq_true] at h1 h2
  rw [hdT, hsT, Bool.and_eq_true]
  exact ⟨h1 j hj, h2 j hj⟩

theorem normObj_k' : normObjCheck = true := by
  have h1 := kNO1
  have h2 := kNO2
  have h3 := kNO3
  simp only [Bool.and_eq_true] at h1 h2 h3
  unfold normObjCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨normBy_of' chS_K chS_P' h1.1.1.1.1.1.1,
    normBy_of' chX1_K chX1_P h1.1.1.1.1.1.2⟩, normBy_of' chX2_K chX2_P h1.1.1.1.1.2⟩,
    normBy_of' chX3_K chX3_P h1.1.1.1.2⟩, normBy_of' chK1_K chK1_P h1.1.1.2⟩,
    normBy_of' chK2_K chK2_P h1.1.2⟩, normBy_of' chA1_K chA1_P h1.2⟩,
    normBy_of' chA2_K chA2_P h2.1.1⟩, normBy_of' chK1A1_K chK1A1_P h2.1.2⟩,
    normBy_of' chK2A2_K chK2A2_P h2.2⟩, normBy_of' chSJ_K chSJ_P h3.1.1.1.1.1.1.1.1.1⟩,
    normBy_of' chA3_K chA3_P h3.1.1.1.1.1.1.1.1.2⟩, normBy_of' chA4_K chA4_P h3.1.1.1.1.1.1.1.2⟩,
    normBy_of' chX8_K chX8_P h3.1.1.1.1.1.1.2⟩, normBy_of' chSig_K chSig_P h3.1.1.1.1.1.2⟩,
    normBy_of' chLam_K chLam_P h3.1.1.1.1.2⟩, normBy_of' chZ2S_K chZ2S_P h3.1.1.1.2⟩,
    normBy_of' chZ_K chZ_P h3.1.1.2⟩, normBy_of' chX1Z_K chX1Z_P h3.1.2⟩,
    normBy_of' chP2_K chP2_P kNO4⟩, normBy_of' chX6Z_K chX6Z_P h3.2⟩

theorem normL_k' : normLCheck = true := by
  have h := normBy_of' chL_K chL_P kNL
  unfold normBy at h
  unfold normLCheck
  rw [lvL]
  exact h

section

open CFSG.Monster.B.Co2

theorem p4_k' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ p4At a = true := by
  have hk : prodLazyK 693 (693 * 10) CK1.LR CK1.TR p4L 3 0 [] = true := by
    refine p4_all fun s hs => ?_
    interval_cases s
    exacts [kQ0, kQ1, kQ2, kQ3, kQ4, kQ5, kQ6, kQ7, kQ8, kQ9, kQ10, kQ11, kQ12, kQ13, kQ14, kQ15,
      kQ16, kQ17, kQ18, kQ19, kQ20, kQ21, kQ22, kQ23, kQ24, kQ25, kQ26, kQ27, kQ28, kQ29]
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chK1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hk x hx
  exact ⟨_, hR, p4_L' hL hf⟩

theorem l1_k' : ∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ l1At a = true := by
  have hk : prodLazyK 693 (693 * 10) CA4.LR CA4.TR
      (fun L => strictB (prodL 693 10 (mask 10) L) (l1K (l1Words.map wK).reverse)) 2 0 [] =
        true := by
    rw [prodLazyK_succ, cA4_size]
    refine allN_of_forall fun a ha => ?_
    have h : l1Run a = true := by
      interval_cases a
      exacts [kL1_0, kL1_1, kL1_2, kL1_3, kL1_4, kL1_5, kL1_6, kL1_7]
    unfold l1Run at h
    rw [forceL_eq, List.append_nil] at h
    exact h
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA4_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hk x hx
  rw [strictB_eq] at hf
  exact ⟨_, hR, l1_of (prodL_canon hL) hf⟩

end

end CertificateChecks.KernelU6.Sec3
