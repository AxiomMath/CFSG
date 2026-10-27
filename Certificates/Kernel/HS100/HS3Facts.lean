module

public import Certificates.Kernel.HS100.HS3Data
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.HS100.Five
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.Misc.ChainTailSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (arrBind_sound pow_unpack' conj_unpack' eqA_unpack' permB_of_pp pp_ppow
  permB)
open CFSG.KC.Misc.ChainTail (ptailK_sound)
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Certificates.Native
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
open CFSG.Monster.B.Co2 (allLt_iff)

theorem allLt_eq (n : ℕ) (p : ℕ → Bool) : allLt n p = allN n p :=
  Bool.eq_iff_iff.2 ⟨fun h => allN_intro (allLt_iff.1 h), fun h => allLt_iff.2 (allN_spec h)⟩

theorem hX : hsX = unpack 100 7 (H3 0) := arrBind_sound HS3.bX

theorem hC3 : hsC3 = unpack 100 7 (H3 1) := arrBind_sound HS3.bC3

theorem hGs {k : ℕ} (hk : k < 2) : hsGs[k]! = unpack 100 7 (H3 (k + 2)) :=
  arrBind_sound (allN_spec HS3.bGs k hk)

theorem hConj {j : ℕ} (hj : j < 8) : hsConjs.getD j #[] = unpack 100 7 (H3 (j + 4)) :=
  arrBind_sound (allN_spec HS3.bConjs j hj)

theorem hBlk : hsBlk = unpack 100 3 (HB 0) := by
  have h := HS3.bBlk
  rw [Bool.and_eq_true] at h
  exact arrBind_sound h.1

theorem hRep : hsRep = unpack 5 7 (HR 0) := by
  have h := HS3.bBlk
  rw [Bool.and_eq_true] at h
  exact arrBind_sound h.2

theorem hR0 : hsR0 = unpack 5 3 (FC.G 0) := by
  have h := HS3.bF
  rw [Bool.and_eq_true] at h
  exact arrBind_sound h.1

theorem hR1 : hsR1 = unpack 5 3 (FC.G 1) := by
  have h := HS3.bF
  rw [Bool.and_eq_true] at h
  exact arrBind_sound h.2

theorem ppH {j : ℕ} (hj : j < 12) : PP 100 7 (H3 j) := PP_of_permOK hw (allN_spec HS3.perm j hj)

theorem siftH {j : ℕ} (hj : j < 12) : siftA 100 hs100PLevels hs100BaseArr 0 (unpack 100 7 (H3 j)) =
    true :=
  siftP rfl (allN_spec HS3.sift j hj)

theorem keys5 : CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.hsKeys = [0, 1, 2, 3, 4] := rfl

theorem cc_gens : hsGs.size = CC.ng ∧ ∀ k < CC.ng, hsGs[k]! = unpack 100 7 (CC.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec HS3.gensC k hk2)]
  exact hGs hk2

theorem cc_perm : ∀ k < CC.ng, permOK 100 7 (mask 7) (100 * 7) (CC.G k)
    (pinvS 100 7 (mask 7) (CC.G k)) = true := by
  intro k hk
  have hk2 : k < 2 := hk
  rw [Nat.eq_of_beq_eq_true (allN_spec HS3.gensC k hk2)]
  exact allN_spec HS3.perm _ (by omega)

theorem cc_pts : (hsCCert ()).pts = Array.ofFn (n := CC.N) fun i => unpack 100 7 (CC.T i.val) := by
  unfold hsCCert
  rw [keys5]
  exact enumBfs_pts_base cc_gens.1 cc_gens.2 CC.ok (by decide) CC.keys (by decide)

theorem cc_enumOK : enumOK 100 hsGs CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.hsKeys (hsCCert ()) =
    true := by
  unfold hsCCert
  rw [keys5]
  exact enumOK_of_bfsK_base cc_gens.1 cc_gens.2 cc_perm CC.ok (by decide) CC.keys (by decide)

theorem pc_gens : (#[hsX, hsC3] : Array (Array ℕ)).size = PC.ng ∧
    ∀ k < PC.ng, (#[hsX, hsC3] : Array (Array ℕ))[k]! = unpack 100 7 (PC.G k) := by
  have h := HS3.gensP
  rw [Bool.and_eq_true] at h
  refine ⟨rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true h.1]
    exact hX
  · rw [Nat.eq_of_beq_eq_true h.2]
    exact hC3

theorem pc_perm : ∀ k < PC.ng, permOK 100 7 (mask 7) (100 * 7) (PC.G k)
    (pinvS 100 7 (mask 7) (PC.G k)) = true := by
  have h := HS3.gensP
  rw [Bool.and_eq_true] at h
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true h.1]
    exact allN_spec HS3.perm 0 (by norm_num)
  · rw [Nat.eq_of_beq_eq_true h.2]
    exact allN_spec HS3.perm 1 (by norm_num)

theorem pc_pts : (hsPCert ()).pts = Array.ofFn (n := PC.N) fun i => unpack 100 7 (PC.T i.val) := by
  unfold hsPCert
  rw [keys5]
  exact enumBfs_pts_base pc_gens.1 pc_gens.2 PC.ok (by decide) PC.keys (by decide)

theorem pc_enumOK : enumOK 100 #[hsX, hsC3] CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.hsKeys
    (hsPCert ()) = true := by
  unfold hsPCert
  rw [keys5]
  exact enumOK_of_bfsK_base pc_gens.1 pc_gens.2 pc_perm PC.ok (by decide) PC.keys (by decide)

theorem fc_gens : (#[hsR0, hsR1] : Array (Array ℕ)).size = FC.ng ∧
    ∀ k < FC.ng, (#[hsR0, hsR1] : Array (Array ℕ))[k]! = unpack 5 3 (FC.G k) := by
  refine ⟨rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · exact hR0
  · exact hR1

theorem fc_perm : ∀ k < FC.ng, permOK 5 3 (mask 3) (5 * 3) (FC.G k)
    (pinvS 5 3 (mask 3) (FC.G k)) = true := fun k hk => allN_spec HS3.permF k hk

theorem range5 : ([0, 1, 2, 3, 4] : List ℕ) = List.range 5 := rfl

theorem fc_pts : (hsFiveCert ()).pts = Array.ofFn (n := FC.N) fun i => unpack 5 3 (FC.T i.val) := by
  unfold hsFiveCert
  rw [range5]
  exact enumBfs_pts fc_gens.1 fc_gens.2 FC.ok (by decide)

theorem fc_enumOK : enumOK 5 #[hsR0, hsR1] [0, 1, 2, 3, 4] (hsFiveCert ()) = true := by
  unfold hsFiveCert
  rw [range5]
  exact enumOK_of_bfsK fc_gens.1 fc_gens.2 fc_perm FC.ok (by decide)

theorem sizes : (hsCCert ()).pts.size = 360 ∧ (hsPCert ()).pts.size = 9 ∧
    (hsFiveCert ()).pts.size = 120 := by
  have h := HS3.sizes
  simp only [Bool.and_eq_true] at h
  rw [cc_pts, pc_pts, fc_pts, Array.size_ofFn, Array.size_ofFn, Array.size_ofFn]
  exact ⟨Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem pp0 : PP 100 7 (H3 0) := ppH (by norm_num)

theorem x_pow (e : ℕ) : powArr 100 hsX e = unpack 100 7 (ppow 100 7 (mask 7) (pidn 100 7) (H3 0) e) := by
  rw [hX]
  exact pow_unpack' hw (permB_of_pp pp0) e

theorem x3 : (eqA 100 (powArr 100 hsX 3) (idA 100) && !eqA 100 hsX (idA 100)) = true := by
  rw [x_pow, idA_eq hw, eqA_PP (pp_ppow hw pp0 3) (PP.id hw), hX, eqA_PP pp0 (PP.id hw)]
  exact HS3.x3

theorem rels3 : relsOK 100 hs100BaseArr hsX hsRels = true := by
  unfold relsOK
  simp only [x_pow, unpack_getElem!]
  quickRfl

theorem comm3 : allLt hsGs.size (fun k => commA 100 hsGs[k]! hsX) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := hk
  have pk : PP 100 7 (H3 (k + 2)) := ppH (by omega)
  rw [hGs hk2, hX, commA, compA_PP pk pp0, compA_PP pp0 pk, eqA_PP (pk.mul pp0) (pp0.mul pk)]
  exact allN_spec HS3.comm k hk2

theorem sift3 : allLt hsGs.size (fun k => siftA 100 (rawLevels 100 hs100StrongArrs hs100BaseArr)
    hs100BaseArr 0 hsGs[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := hk
  rw [hGs hk2]
  exact siftH (by omega)

theorem pow5_get : ∀ e < (pow5A 100 hsX).size,
    (pow5A 100 hsX)[e]! = unpack 100 7 (ppow 100 7 (mask 7) (pidn 100 7) (H3 0) e) := by
  intro e he
  rw [getElem!_pos _ e he]
  simp only [pow5A, Array.getElem_ofFn]
  exact x_pow e

theorem ptail3 : ptailOK 100 (rawLevels 100 hs100StrongArrs hs100BaseArr) hs100BaseArr hsX
    (pow5A 100 hsX) hsRels (hsCCert ()).pts.toList hs100BaseArr.size 0 (idA 100) = true := by
  have hsz : hs100BaseArr.size = 5 := by decide
  rw [hsz]
  have hbr : ∀ k < rcnt (HC.LR 0), br3 k = true := by
    rw [Nat.eq_of_beq_eq_true HS3.rc]
    exact allN_spec HS3.br
  have hE : (hsCCert ()).pts.toList = (List.range 360).map fun e => unpack 100 7 (CC.T e) := by
    rw [cc_pts]
    exact pts_toList (N := CC.N) fun e => unpack 100 7 (CC.T e)
  have hEp : ∀ e < 360, permB 100 7 (CC.T e) = true :=
    fun e he => permB_of_pp (PP_pts CC.ok cc_perm e he)
  have hrels : ∀ r ∈ hsRels, r.2.2 < (pow5A 100 hsX).size := by
    intro r hr
    have hs : (pow5A 100 hsX).size = 5 := by simp [pow5A]
    rw [hs]
    simp only [hsRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num
  exact ptailK_sound binds HC.perm HC.hl hX (permB_of_pp pp0) pow5_get hrels hE hEp (by norm_num)
    hbr

theorem validX : validA 100 hsX = true := by
  rw [hX]
  exact CFSG.KC.BfsPin.validA_unpack (allN_spec HS3.perm 0 (by norm_num))

theorem siftX : siftA 100 hs100PLevels hs100BaseArr 0 hsX = true := by
  rw [hX]
  exact siftH (by norm_num)

theorem cent3 : hsCentOK () = true := by
  have hx3 := x3
  rw [Bool.and_eq_true] at hx3
  unfold hsCentOK centOK
  rw [validX, siftX, hx3.1, hx3.2, rels3, cc_enumOK, sizes.1, comm3, sift3, ptail3]
  rfl

theorem pc_get {k : ℕ} (hk : k < PC.N) : (hsPCert ()).pts[k]! = unpack 100 7 (PC.T k) := by
  rw [pc_pts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem syl_pt {k : ℕ} (hk : k < 9) : (eqA 100 (hsPCert ()).pts[k]! (idA 100) ||
    hsConjs.any fun g => validA 100 g && siftA 100 hs100PLevels hs100BaseArr 0 g &&
      eqA 100 (conjA 100 g (hsPCert ()).pts[k]!) hsX) = true := by
  have hkN : k < PC.N := hk
  have hT : PP 100 7 (PC.T k) := PP_pts PC.ok pc_perm k hkN
  have h := allN_spec HS3.conj k hk
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨h8, h⟩ := h
  have h8' : W3 k < 8 := Nat.blt_eq ▸ h8
  have hlen : hsConjs.length = 8 := rfl
  rw [pc_get hkN, Bool.or_eq_true]
  rcases h with h | h
  · left
    rw [idA_eq hw, eqA_PP hT (PP.id hw)]
    exact h
  · right
    rw [List.any_eq_true]
    refine ⟨hsConjs.getD (W3 k) #[], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact h8')]
      exact List.getElem_mem _
    · have hg : PP 100 7 (H3 (W3 k + 4)) := ppH (by omega)
      rw [hConj h8', Bool.and_eq_true, Bool.and_eq_true,
        conj_unpack' hw (permB_of_pp hg) (permB_of_pp hT), hX, eqA_PP (hg.mul (hT.mul hg.inv)) pp0]
      exact ⟨⟨CFSG.KC.BfsPin.validA_unpack (allN_spec HS3.perm _ (by omega)), siftH (by omega)⟩, h⟩

theorem syl3 : hsSylowOK () = true := by
  unfold hsSylowOK
  have hs : siftA 100 hs100PLevels hs100BaseArr 0 hsC3 = true := by
    rw [hC3]
    exact siftH (by norm_num)
  rw [pc_enumOK, sizes.2.1, hs, allLt_iff.2 fun k hk => syl_pt hk]
  rfl

theorem blk_pt {k : ℕ} (hk : k < 360) : (allLt 100 (fun p => !(hsF.contains p) ||
      (hsF.contains (hsEl k)[p]! && hsBlk[(hsEl k)[p]!]! ==
        hsBlk[(hsEl k)[hsRep[hsBlk[p]!]!]!]!)) &&
    (!(allLt 100 (fun p => !(hsF.contains p) || hsBlk[(hsEl k)[p]!]! == hsBlk[p]!)) ||
      eqA 100 (powArr 100 (hsEl k) 3) (idA 100))) = true := by
  have hkN : k < CC.N := hk
  have hT : PP 100 7 (CC.T k) := PP_pts CC.ok cc_perm k hkN
  have he : hsEl k = unpack 100 7 (CC.T k) := by
    rw [hsEl, cc_pts, getElem!_pos _ k (by simpa using hkN), Array.getElem_ofFn]
  rw [he, pow_unpack' hw (permB_of_pp hT), idA_eq hw, eqA_PP (pp_ppow hw hT 3) (PP.id hw), hBlk,
    hRep]
  simp only [allLt_eq, unpack_getElem!]
  exact allN_spec HS3.blk k hk

theorem blk3 : hsBlockOK () = true := by
  have h2 := HS3.lit2
  have h3 := HS3.lit3
  simp only [Bool.and_eq_true] at h2 h3
  unfold hsBlockOK
  have hg0 : hsGs[0]! = unpack 100 7 (H3 2) := hGs (k := 0) (by norm_num)
  have hg1 : hsGs[1]! = unpack 100 7 (H3 3) := hGs (k := 1) (by norm_num)
  have e1 : allLt 100 (fun i => (hsX[i]! == i) == hsF.contains i) = true := by
    rw [hX]
    simp only [allLt_eq, unpack_getElem!]
    exact h2.1.1
  have e2 : allLt 100 (fun i => if hsF.contains i then decide (hsBlk[i]! < 5) else
      hsBlk[i]! == 5) = true := by
    rw [hBlk]
    simp only [allLt_eq, unpack_getElem!]
    exact h2.1.2
  have e3 : allLt 5 (fun b => hsF.contains hsRep[b]! && hsBlk[hsRep[b]!]! == b) = true := by
    rw [hBlk, hRep]
    simp only [allLt_eq, unpack_getElem!]
    exact h2.2
  have e4 : allLt 5 (fun b => hsBlk[(hsGs[0]!)[hsRep[b]!]!]! == hsR0[b]!) = true := by
    rw [hBlk, hRep, hg0, hR0]
    simp only [allLt_eq, unpack_getElem!]
    exact h3.1
  have e5 : allLt 5 (fun b => hsBlk[(hsGs[1]!)[hsRep[b]!]!]! == hsR1[b]!) = true := by
    rw [hBlk, hRep, hg1, hR1]
    simp only [allLt_eq, unpack_getElem!]
    exact h3.2
  have e6 : allLt (hsCCert ()).pts.size (fun k => allLt 100 (fun p => !(hsF.contains p) ||
      (hsF.contains (hsEl k)[p]! && hsBlk[(hsEl k)[p]!]! ==
        hsBlk[(hsEl k)[hsRep[hsBlk[p]!]!]!]!)) &&
      (!(allLt 100 (fun p => !(hsF.contains p) || hsBlk[(hsEl k)[p]!]! == hsBlk[p]!)) ||
        eqA 100 (powArr 100 (hsEl k) 3) (idA 100))) = true := by
    rw [sizes.1]
    exact allLt_iff.2 fun k hk => blk_pt hk
  rw [e1, e2, e3, e6, e4, e5, fc_enumOK, sizes.2.2]
  rfl

theorem hsThree : hsThreeOK () = true := by
  unfold hsThreeOK
  rw [cent3, syl3, blk3]
  rfl

end CertificateChecks.KernelHS100

end
