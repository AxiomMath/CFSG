
module

public import Certificates.Kernel.SporSch.Co2M.Ker
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.Co2LE CFSG.KS.MatRep CFSG.KS.MatInj
open CFSG.RankThree.Native.F2 CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native

@[expose] noncomputable def pairRow (k0 : ℕ) : Bool :=
  allN 32 fun k1 => !candK k0 k1 || ([[0, 0], [0, 9]] : List (List ℕ)).contains [k0, k1]

theorem pairs_rows : ∀ t < 32, pairRow t = true := by
  kc_cover 1

theorem pairs_ok : allLt 32 (fun k0 => allLt 32 fun k1 =>
    !candK k0 k1 || ([[0, 0], [0, 9]] : List (List ℕ)).contains [k0, k1]) = true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k0 h0
  rw [CFSG.Monster.B.Co2.allLt_iff]
  exact allN_spec (pairs_rows k0 h0)

theorem derivD_len : derivD.length = 10 := by decide +kernel

theorem candOK_eq {k0 k1 : ℕ} (h0 : k0 < 32) (h1 : k1 < 32) :
    candOK kerData k0 k1 = candK k0 k1 := by
  obtain ⟨hx1, hx2, hfix, hadd, -, hrl, hrw, haw, -⟩ := wfacts
  have hc := candRep h0 h1
  have hcl : (candT k0 k1).length = 2 := rfl
  have hX := repT_extend good V_size mmK_eq I22_eq derivD hc (by rewrite [hcl]; exact hx1)
  have hD := repT_extend good V_size mmK_eq I22_eq derivD dRepL (by exact hx1)
  have hL := repT_extend good V_size mmK_eq I22_eq localRec.dStrongDerivations hc
    (by rewrite [hcl]; exact hx2)
  have hks := ksm_ok
  unfold candOK candK
  rewrite [hfix, hadd, hrl]
  have eD : kerData.derivD = derivD := rfl
  have eL : kerData.derivLegacy = localRec.dStrongDerivations := rfl
  have eR : kerData.rWords = localRec.rWords := rfl
  have ed : kerData.d = dArrs := rfl
  have er : kerData.r = rArrs := rfl
  rewrite [eD, eL, eR, ed, er]
  congr 1
  congr 1
  · refine all_congr' fun j hj => ?_
    have hj' : j = 6 ∨ j = 7 ∨ j = 8 := by simpa using hj
    have hjl : j < 12 := by omega
    rewrite [eqA_rep (repT_get hX (by rewrite [extP_length, hcl, derivD_len]; omega))
      (repT_get hD (by rewrite [extP_length, derivD_len]; change j < 2 + 10; omega))]
    congr 1
    have e := Nat.eq_of_beq_eq_true (allN_spec hks.1 (j - 6) (by omega))
    have ej : Nat.add 6 (j - 6) = j := by rewrite [Nat.add_eq]; omega
    rewrite [ej] at e
    rewrite [e]
    rfl
  · refine allLt_congr' fun i hi => ?_
    have hw := hrw i hi
    have hLl : (extP mmK I22 (candT k0 k1) localRec.dStrongDerivations).length = 7 := by
      rewrite [extP_length, hcl]
      rfl
    rewrite [eqA_rep (rep_wordArr good V_size mmK_eq I22_eq hL (by rewrite [hLl]; exact hw))
      (repT_get rRep (by rewrite [r_len]; exact hi)), ← Nat.eq_of_beq_eq_true (allN_spec rg_ok i hi)]
    rfl
  · refine all_congr' fun w hw => ?_
    have hw' : w = addW := by simpa using hw
    subst hw'
    rewrite [eqA_rep (rep_wordArr good V_size mmK_eq I22_eq hc (by rewrite [hcl]; exact haw))
      (rep_wordArr good V_size mmK_eq I22_eq dRepL (by exact haw)), Nat.eq_of_beq_eq_true hks.2]
    rfl

theorem kerSift_eq {g : Array ℕ} {X X' : ℕ} (hg : Rep 22 co2PackedVecs g X X') {i : ℕ}
    (hb : bindK (PV 0) (KSG i) X X' = true) : g = unpack 2300 12 (KSG i) := by
  rewrite [hg.1, (bindK_sound good V_size (fun _ hi => V_get hi) rfl hb).1]
  rfl

theorem sift_at {g : Array ℕ} {X X' : ℕ} (hg : Rep 22 co2PackedVecs g X X') {i : ℕ} (hi : i < 4)
    (hb : bindK (PV 0) (KSG i) X X' = true) :
    siftA 2300 levelsS localRec.chains.S.baseArr 0 g = true :=
  Co2SS.sift_of (kerSift_eq hg hb) (allN_spec ksg_range i hi) (allN_spec ksg_sift i hi)

theorem commA_rep {a b : Array ℕ} {p q : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (hb : Rep 22 co2PackedVecs b q.1 q.2) :
    commA a b = Nat.beq (md (cmpP p q).1) (md (cmpP q p).1) := by
  unfold commA
  exact eqA_rep (rep_cmp ha hb) (rep_cmp hb ha)

theorem eqA_cmp {a b c d : Array ℕ} {p q r s : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (hb : Rep 22 co2PackedVecs b q.1 q.2) (hc : Rep 22 co2PackedVecs c r.1 r.2)
    (hd : Rep 22 co2PackedVecs d s.1 s.2) :
    eqA 2300 (compA 2300 a b) (compA 2300 (compA 2300 c d) a) =
      Nat.beq (md (cmpP p q).1) (md (cmpP (cmpP r s) p).1) :=
  eqA_rep (rep_cmp ha hb) (rep_cmp (rep_cmp hc hd) ha)

theorem ker_check : kerCheck kerData = true := by
  obtain ⟨hx1, hx2, hfix, hadd, hsurv, hrl, hrw, haw, hw1, hw2, hw3, hw4⟩ := wfacts
  have hD := repT_extend good V_size mmK_eq I22_eq derivD dRepL (by exact hx1)
  have hDl : (extP mmK I22 dTL derivD).length = 12 := by rewrite [extP_length, derivD_len]; rfl
  have hb := ksg_bind
  have hz0 : centerIdxR.getD 0 0 = 0 := rfl
  obtain ⟨hdz1, hdz2, hdz3⟩ : Nat.beq (md (cmpP (RC 0, RC 2) zP).1) (md (cmpP zP (RC 0, RC 2)).1) =
      true ∧ Nat.beq (md (cmpP (RC 1, RC 3) zP).1) (md (cmpP zP (RC 1, RC 3)).1) = false ∧
      Nat.beq (md (cmpP zP (RC 1, RC 3)).1) (md (cmpP (cmpP (RC 1, RC 3) (ZM 9, ZM 9)) zP).1) =
        true := by
    have h := dz_ok
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hd0 : Rep 22 co2PackedVecs kerData.d[0]! (RC 0) (RC 2) := rcrep 0 (by norm_num)
  have hd1 : Rep 22 co2PackedVecs kerData.d[1]! (RC 1) (RC 3) := rcrep 1 (by norm_num)
  have hzz : Rep 22 co2PackedVecs kerData.z zP.1 zP.2 := zRep
  unfold kerCheck
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hsurv⟩, ?_⟩, ?_⟩, allInv_of hD⟩, hw1⟩, hw2⟩, hw3⟩, hw4⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · change ((centerIdxR.map fun k => enumR.elems[k]!).toArray).size = 32
    rewrite [List.size_toArray, List.length_map]
    rfl
  · change dArrs.size = 2
    rewrite [dRep.1, d_len]
    rfl
  · rewrite [hrl]
    exact (rRep.1.trans r_len)
  · rewrite [CFSG.Monster.B.Co2.allLt_iff]
    intro k0 h0
    rewrite [CFSG.Monster.B.Co2.allLt_iff]
    intro k1 h1
    have hp := pairs_ok
    rewrite [CFSG.Monster.B.Co2.allLt_iff] at hp
    have hp' := hp k0 h0
    rewrite [CFSG.Monster.B.Co2.allLt_iff] at hp'
    rewrite [candOK_eq h0 h1, hsurv]
    exact hp' k1 h1
  · rewrite [CFSG.Monster.B.Co2.allLt_iff]
    intro k0 h0
    rewrite [CFSG.Monster.B.Co2.allLt_iff]
    intro k1 h1
    have hc := candRep h0 h1
    have hcl : (candT k0 k1).length = 2 := rfl
    rewrite [Bool.and_eq_true]
    exact ⟨allInv_of (repT_extend good V_size mmK_eq I22_eq derivD hc (by rewrite [hcl]; exact hx1)),
      allInv_of (repT_extend good V_size mmK_eq I22_eq localRec.dStrongDerivations hc
        (by rewrite [hcl]; exact hx2))⟩
  · rewrite [hfix]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    have hdl : kerData.derivD.length = 10 := derivD_len
    rewrite [hdl]
    have e : ∀ i < 3, siftA 2300 levelsS localRec.chains.S.baseArr 0
        (extendArrs kerData.d kerData.derivD)[Nat.add 6 i]! = true := fun i hi =>
      sift_at (repT_get hD (by rewrite [hDl, Nat.add_eq]; omega)) (by omega) (allN_spec hb.1 i hi)
    exact ⟨⟨by norm_num, e 0 (by norm_num)⟩, ⟨by norm_num, e 1 (by norm_num)⟩,
      ⟨by norm_num, e 2 (by norm_num)⟩⟩
  · rewrite [hadd]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact sift_at (rep_wordArr good V_size mmK_eq I22_eq dRepL (by exact haw)) (by norm_num) hb.2
  · rewrite [zs_get (by norm_num), hz0]
    have h := (leftEnum_facts vok rrecs rgens (le_refl 2048)).1
    unfold enumR
    rewrite [h, LL_get _ (by norm_num), rrecs.zero, I22_eq, permOfMat_idM good.hd good.nodup good.lt,
      V_size]
    exact eqA_refl _ _
  · rewrite [commA_rep (p := (RC 0, RC 2)) (q := zP) hd0 hzz]
    exact hdz1
  · rewrite [commA_rep (p := (RC 1, RC 3)) (q := zP) hd1 hzz]
    exact hdz2
  · rewrite [eqA_cmp (p := zP) (q := (RC 1, RC 3)) (r := (RC 1, RC 3)) (s := (ZM 9, ZM 9)) hzz hd1 hd1
      (zsRep (by norm_num))]
    exact hdz3

end CertificateChecks.KernelSporSch.Co2M

end
