module

public import Certificates.Kernel.LocalComp.Fi24TwoB.H15027
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CertificateChecks.KernelSpor.Fi24C
open CertificateChecks.KernelSpor CertificateChecks.KernelLC
open CFSG.RankThree.Native (validA)
open CFSG.Certificates.ChainArrays (lev)

@[expose] noncomputable def wK (i : Nat) : Nat :=
  CFSG.KS.Raw.wordK 504 9 (mask 9) (pidn 504 9) Fi24BKd.S Fi24BKd.SI fi24KdStabWords[i]!

theorem kWords : allN 2 (fun i => bAnd(wordEqK 504 9 (mask 9) (pidn 504 9) Fi24BKd.S Fi24BKd.SI 16
    fi24KdStabWords[i]! (wK i), bAnd(canonK 504 9 (mask 9) (504 * 9) (wK i),
    permOK 504 9 (mask 9) (504 * 9) (wK i) (pinvS 504 9 (mask 9) (wK i))))) = true := by quickRfl

theorem kWSift : allN 2 (fun i => siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24BKd.LR
    Fi24BKd.TRI Fi24BKd.BP 7 0 (wK i)) = true := by quickRfl

theorem kWFix : (Nat.beq (pg 9 (mask 9) (wK 0) 0) 0 && Nat.beq (pg 9 (mask 9) (wK 1) 0) 0 &&
    allN 504 (fun p => Nat.beq p 0 || !Nat.beq (pg 9 (mask 9) (wK 0) p) p ||
      !Nat.beq (pg 9 (mask 9) (wK 1) p) p)) = true := by quickRfl

theorem kLev : Nat.beq (rcnt (Fi24BKd.LR 0)) 504 = true := by quickRfl

theorem word_facts {i : Nat} (hi : i < 2) :
    wordA 504 fi24KdStrong (rawInvs 504 fi24KdStrong) fi24KdStabWords[i]! = unpack 504 9 (wK i) ∧
      Cn 504 9 (wK i) ∧
      permOK 504 9 (mask 9) (504 * 9) (wK i) (pinvS 504 9 (mask 9) (wK i)) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kWords i hi)
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  refine ⟨?_, h3, h4⟩
  rw [dS]
  exact (wordEqK_sound ⟨by simp, fun j hj => ofFn_get hj⟩ permD h1).1

theorem word_sift {i : Nat} (hi : i < 2) :
    siftA 504 fi24KdLevels fi24KdBase.toArray 0 (unpack 504 9 (wK i)) = true := by
  obtain ⟨-, hc, -⟩ := word_facts hi
  unfold fi24KdLevels
  rw [dS, siftK_eq bindsD permD Fi24BKd.hl rfl (hi_of hc) (range_of_canonK hc)]
  exact allN_spec kWSift i hi

theorem hd : Orb.Hd 504 fi24KdStrong fi24KdBase.toArray 5 fi24KdWords := by
  obtain ⟨h1, h2⟩ := Orb.rawHeadOK_of bindsD Fi24BKd.head
  rw [← dS] at h1 h2
  rw [← Fi24BW.dW] at h2
  exact Orb.hd_of_head h1 h2

theorem lev_size : (lev 504 fi24KdStrong fi24KdBase.toArray 0).pts.size = 504 := by
  have h := rawOrbitSizesK_sound bindsD permD Fi24BKd.hl
  rw [← dS] at h
  have h0 := congrArg (fun l => l[0]!) h
  simp only [rawOrbitSizes] at h0
  have hs : 0 < (rawLevels 504 fi24KdStrong fi24KdBase.toArray).size := by
    simp [rawLevels, fi24KdBase]
  have e1 : (List.map (fun L => L.pts.size) (rawLevels 504 fi24KdStrong fi24KdBase.toArray).toList)[0]! =
      (rawLevels 504 fi24KdStrong fi24KdBase.toArray)[0]!.pts.size := by
    rw [getElem!_pos _ 0 (by simpa using hs), List.getElem_map, Array.getElem_toList,
      ← getElem!_pos _ 0 hs]
  have e2 : (List.map (fun i => rcnt (Fi24BKd.LR i)) (List.range 7))[0]! = rcnt (Fi24BKd.LR 0) := by
    rw [getElem!_pos _ 0 (by simp), List.getElem_map, List.getElem_range]
  rw [e1, e2] at h0
  rw [lev, h0]
  exact Nat.eq_of_beq_eq_true kLev

theorem gen_le : Orb.Gen 504 fi24KdStrong 5 ≤ fi24Kd := by
  unfold Orb.Gen
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact permOfArr_mem_fi24Kd chainsOK j.2

theorem pos_lt {p : Nat} (hp : p < 504) :
    (lev 504 fi24KdStrong fi24KdBase.toArray 0).pos[p]! <
      (lev 504 fi24KdStrong fi24KdBase.toArray 0).pts.size := by
  have F := Orb.lev_facts hd (i := 0) (by simp [fi24KdBase])
  set L := lev 504 fi24KdStrong fi24KdBase.toArray 0
  have hsz := lev_size
  have himg : (Finset.range 504).image (fun k => L.pts[k]!) = Finset.range 504 := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_range.2 (F.pts_lt k (by rw [hsz]; exact Finset.mem_range.1 hk))
    · rw [Finset.card_image_of_injOn]
      intro a ha b hb e
      have ha' : a < L.pts.size := by rw [hsz]; exact Finset.mem_range.1 ha
      have hb' : b < L.pts.size := by rw [hsz]; exact Finset.mem_range.1 hb
      have e' : L.pts[a]! = L.pts[b]! := e
      rw [← F.pos_pts a ha', ← F.pos_pts b hb', e']
  have hm : p ∈ (Finset.range 504).image (fun k => L.pts[k]!) := by
    rw [himg]
    exact Finset.mem_range.2 hp
  obtain ⟨k, hk, hkp⟩ := Finset.mem_image.1 hm
  have hk' : k < L.pts.size := by rw [hsz]; exact Finset.mem_range.1 hk
  rw [← hkp, F.pos_pts k hk']
  exact hk'

theorem trans_ok : ∀ p < 504,
    (validA 504 (fi24KdLevels[0]!).tr[(fi24KdLevels[0]!).pos[p]!]! &&
      ((fi24KdLevels[0]!).tr[(fi24KdLevels[0]!).pos[p]!]!)[0]! == p &&
      siftA 504 fi24KdLevels fi24KdBase.toArray 0 (fi24KdLevels[0]!).tr[(fi24KdLevels[0]!).pos[p]!]!)
      = true := by
  intro p hp
  have hi : 0 < fi24KdBase.toArray.size := by simp [fi24KdBase]
  have F := Orb.lev_facts hd hi
  have hk := pos_lt hp
  have hr := Orb.rep_tr hd hi hk
  obtain ⟨hmem, happ⟩ := Orb.tr_spec hd hi _ hk
  have hpts := F.pts_pos p hp hk
  have hL : fi24KdLevels[0]! = lev 504 fi24KdStrong fi24KdBase.toArray 0 := rfl
  rw [hL]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨CFSG.RankThree.Native.F2.validA_of_rep hr, ?_⟩, sift_of_mem hr ?_⟩
  · have hb0 : fi24KdBase.toArray[0]! = 0 := rfl
    rw [hr.apply (by norm_num : 0 < 504)]
    have e : (⟨0, by norm_num⟩ : Fin 504) = ⟨fi24KdBase.toArray[0]!, Orb.Hd.base_lt hd 0 hi⟩ := by
      simp [hb0]
    rw [e, happ, hpts]
  · exact gen_le (by rw [← Orb.Fix_zero]; exact hmem)

theorem transOK : fi24KdTransOK = true := by
  have hw0 := word_facts (i := 0) (by norm_num)
  have hw1 := word_facts (i := 1) (by norm_num)
  have hf := kWFix
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨f0, f1⟩, f2⟩ := hf
  unfold fi24KdTransOK fi24KdLevels
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hw0.1, hw1.1]
  refine ⟨⟨⟨⟨⟨⟨⟨allLt_iff.2 trans_ok, validA_unpack hw0.2.2⟩, validA_unpack hw1.2.2⟩,
    word_sift (by norm_num)⟩, word_sift (by norm_num)⟩, ?_⟩, ?_⟩, allLt_iff.2 fun p hp => ?_⟩
  · rw [Fi24C.unpack_get' (by norm_num : 0 < 504)]
    exact Nat.eq_of_beq_eq_true f0
  · rw [Fi24C.unpack_get' (by norm_num : 0 < 504)]
    exact Nat.eq_of_beq_eq_true f1
  · have h := allN_spec f2 p hp
    rw [Fi24C.unpack_get' hp, Fi24C.unpack_get' hp]
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (by simpa using Nat.eq_of_beq_eq_true h))
    · refine Or.inl (Or.inr (bne_iff_ne.2 fun e => ?_))
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h
    · refine Or.inr (bne_iff_ne.2 fun e => ?_)
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h

end CertificateChecks.KernelLC.Fi24B

end
