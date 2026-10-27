module

public import Certificates.Kernel.HatM.Words
public import Certificates.Kernel.HatM.Checks
public import CFSG.Certificates.Kernel.HatChkKSound
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.Misc.ArrBind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHatM

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Quasithin.H13.Ch4.HatChk CFSG.Quasithin.H13.Ch4.HatM CFSG.KC.HatChkK
open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu
open CFSG.KC.Enum (pg pcomp pidn permOK)
open CFSG.KS (mask pinvS)
open CFSG.KS.Raw (unpack wordK lettersK)
open CFSG.KC.Misc.ArrEnum (permB arrBind arrBind_sound pp_of_permB permB_of_pp)
open CFSG.KC.B3S3K (BindA enum_of validA_of)
open CFSG.KC.BfsPin (PP compA_PP invCand_PP)

theorem allR {m : ℕ} {f : ℕ → Bool} (h : (List.range m).all f = true) : ∀ k < m, f k = true :=
  fun k hk => List.all_eq_true.1 h k (List.mem_range.2 hk)

theorem imageList_arr24 (g : Equiv.Perm (Fin 24)) : imageList g = (arr24 g).toList := by
  unfold imageList arr24
  rw [Array.toList_ofFn]

theorem arr24_of_img {g : Equiv.Perm (Fin 24)} {P : ℕ}
    (h : imageList g = (unpack 24 5 P).toList) : arr24 g = unpack 24 5 P :=
  Array.toList_inj.mp (by rw [← imageList_arr24]; exact h)

theorem imgAB : ∀ j < [m24gA, m24gB].length,
    imageList ([m24gA, m24gB].getD j 1) = (unpack 24 5 (AB j)).toList := by
  intro j hj
  have hj' : j < 2 := hj
  interval_cases j
  · change imageList m24gA = _
    rw [imageList_arr24, arrBind_sound bA]
  · change imageList m24gB = _
    rw [imageList_arr24, arrBind_sound bB]

theorem permAB : ∀ j < [m24gA, m24gB].length,
    permOK 24 5 (mask 5) (24 * 5) (AB j) (ABI j) = true := fun j hj => allR pAB j hj

theorem imgId : imageList (1 : Equiv.Perm (Fin 24)) = (unpack 24 5 (pidn 24 5)).toList := by
  rw [imageList_arr24, arrBind_sound bId]

theorem parseWord_eq (s : String) : parseWord s = s.toList.map letterCode := rfl

theorem arr24_of_wordOK {s : String} {P : ℕ} (h : wordOK s.toList P = true) :
    arr24 (m24W s) = unpack 24 5 P := by
  unfold wordOK at h
  rw [Bool.and_eq_true] at h
  have e := CFSG.KS.SporSch.CodesImg.evalCodes_img sz5 imgAB permAB imgId
    (wd := parseWord s) (by rw [parseWord_eq]; exact h.1)
  rw [parseWord_eq, Nat.eq_of_beq_eq_true h.2] at e
  exact arr24_of_img e

theorem getD_map_toList (l : List String) {k : ℕ} (hk : k < l.length) :
    (l.map String.toList).getD k [] = (l.getD k "").toList := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
    List.getElem_map]

theorem getElem!_wordGens (l : List String) {k : ℕ} (hk : k < l.length) :
    (l.map fun s => arr24 (m24W s)).toArray[k]! = arr24 (m24W (l.getD k "")) := by
  rw [getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ hk]

theorem lenS1 : s1WordStrs.length = 9 := rfl

theorem lenP1 : p1WordStrs.length = 10 := rfl

theorem gS1 : BindA 24 5 s1Gens 9 ES1.G := by
  refine ⟨nS1, fun k hk => ?_⟩
  have hk' : k < s1WordStrs.length := by rw [lenS1]; exact hk
  have h := allR wS1 k hk
  rw [getD_map_toList _ hk'] at h
  rw [s1Gens, getElem!_wordGens _ hk']
  exact arr24_of_wordOK h

theorem gP1 : BindA 24 5 p1Gens 10 EP1.G := by
  refine ⟨nP1, fun k hk => ?_⟩
  have hk' : k < p1WordStrs.length := by rw [lenP1]; exact hk
  have h := allR wP1 k hk
  rw [getD_map_toList _ hk'] at h
  rw [p1Gens, getElem!_wordGens _ hk']
  exact arr24_of_wordOK h

theorem hr1 : r1Arr = unpack 24 5 (RA 0) := arrBind_sound bR1

theorem hr2 : r2Arr = unpack 24 5 (RA 1) := arrBind_sound bR2

theorem hc : cArr = unpack 24 5 (RA 2) := arr24_of_wordOK wC

theorem pR' : ∀ k < 3, permB 24 5 (RA k) = true := allR pR

theorem gP2 : BindA 24 5 p2Gens 10 EP2.G := by
  refine ⟨nP2, fun k hk => ?_⟩
  have hk1 : k < p1Gens.size := by rw [nP1]; exact hk
  have hC : PP 24 5 (RA 2) := pp_of_permB sz5 (pR' 2 (by decide))
  have hG : PP 24 5 (EP1.G k) := pp_of_permB sz5 (allR pP1 k hk)
  rw [p2Gens, map_getElem! _ _ hk1, gP1.2 k hk, hc, conjA, invCand_PP hC, compA_PP hG hC.inv,
    compA_PP hC (hG.mul hC.inv), Nat.eq_of_beq_eq_true (allR conjP2 k hk)]

theorem hb : base24.toList = ps24 := by decide +kernel

theorem ps_lt : ∀ p ∈ base24.toList, p < 24 := by decide +kernel

theorem tS1 : ∀ i < 512, permB 24 5 (ES1.T i) = true := CFSG.KS.allN_spec ES1.perm

theorem tP1 : ∀ i < 1024, permB 24 5 (EP1.T i) = true := CFSG.KS.allN_spec EP1.perm

theorem tP2 : ∀ i < 1024, permB 24 5 (EP2.T i) = true := CFSG.KS.allN_spec EP2.perm

theorem eS1 : enumOK 24 s1Gens ps24 cS1 = true ∧ cS1.pts.size = 512 ∧
    ∀ i < 512, cS1.pts[i]! = unpack 24 5 (ES1.T i) := by
  have h := enum_of (fuel := 1000) gS1 (allR pS1) ES1.ok ps_lt ES1.keys (by decide)
  rw [hb] at h
  exact h

theorem eP1 : enumOK 24 p1Gens ps24 cP1 = true ∧ cP1.pts.size = 1024 ∧
    ∀ i < 1024, cP1.pts[i]! = unpack 24 5 (EP1.T i) := by
  have h := enum_of (fuel := 2000) gP1 (allR pP1) EP1.ok ps_lt EP1.keys (by decide)
  rw [hb] at h
  exact h

theorem eP2 : enumOK 24 p2Gens ps24 cP2 = true ∧ cP2.pts.size = 1024 ∧
    ∀ i < 1024, cP2.pts[i]! = unpack 24 5 (EP2.T i) := by
  have h := enum_of (fuel := 2000) gP2 (allR pP2) EP2.ok ps_lt EP2.keys (by decide)
  rw [hb] at h
  exact h

theorem ptsP2 : cP2.pts = Array.ofFn (n := 1024) fun i => unpack 24 5 (EP2.T i.val) := by
  apply Array.ext
  · rw [eP2.2.1, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← getElem!_pos cP2.pts i h1]
    exact eP2.2.2 i (by rwa [eP2.2.1] at h1)

theorem memI_eq : (fun i => memL 24 ps24 cP2.pts cP1.pts[i]!) = memI := by
  funext i
  unfold memI
  split
  · next hi =>
    rw [eP1.2.2 i hi, ptsP2, memL_unpack sz5 tP2 (tP1 i hi)]
    rfl
  · rfl

theorem cmI_eq : (fun i j => cmA 24 cP1.pts[i]! cP1.pts[j]!) = cmI := by
  funext i j
  unfold cmI
  split
  · next h =>
    rw [eP1.2.2 i h.1, eP1.2.2 j h.2, cmA_unpack sz5 (tP1 i h.1) (tP1 j h.2)]
  · rfl

theorem clsP_eq : clsP = unpack 1024 6 (CL 0) := by
  have e : clsP = greedyCoverL 24 ps24 cP1.pts cP2.pts := greedyCover_eq 24 ps24 cP1 cP2
  rw [e, greedyCoverL_eq, memI_eq, cmI_eq, eP1.2.1]
  exact arrBind_sound greedy

theorem memC_eq : (fun i => (cP1.pts.map fun t => memL 24 ps24 cP2.pts t)[i]!) = memC := by
  funext i
  unfold memC
  split
  · next hi =>
    rw [map_getElem! _ _ (by rw [eP1.2.1]; exact hi)]
    have e := congrFun memI_eq i
    unfold memI at e
    rw [if_pos hi] at e
    exact e
  · next hi =>
    rw [getElem!_neg]
    · rfl
    · simp only [Array.size_map, eP1.2.1]
      omega

theorem clsC_eq : (fun i => clsP[i]!) = clsC := by
  funext i
  unfold clsC
  rw [clsP_eq]
  split
  · next hi => exact CFSG.KS.Raw.Orb.unpack_get hi
  · next hi =>
    rw [getElem!_neg]
    · rfl
    · simp only [unpack, Array.size_ofFn]
      omega

theorem coverOK_true : coverOK 24 63 ps24 cP1 cP2 clsP = true := by
  rw [coverOK_eq, coverOKL_eq, memC_eq, clsC_eq, cmI_eq, eP1.2.1]
  exact cover

theorem hatM24Check_eq_true : hatM24Check = true := by
  have h1 : fpfA 24 r1Arr = true := by rw [hr1, fpfA_unpack]; exact fpfR1
  have h4 : allLt s1Gens.size (fun k => cmA 24 s1Gens[k]! r1Arr) = true := by
    refine allLt_iff.2 fun k hk => ?_
    rw [gS1.1] at hk
    rw [gS1.2 k hk, hr1, cmA_unpack sz5 (allR pS1 k hk) (pR' 0 (by decide))]
    exact allR cmS1 k hk
  have h5 : fpfPairOK 24 s1Gens cS1 r1Arr = true := by
    rw [hr1, fpfPairOK_unpack sz5 gS1 (allR pS1) eS1.2.1 eS1.2.2 tS1 (pR' 0 (by decide))]
    exact pairS1
  have h6 : validA 24 cArr = true := by rw [hc]; exact validA_of (pR' 2 (by decide))
  have h7 : cmA 24 cArr r2Arr = true := by
    rw [hc, hr2, cmA_unpack sz5 (pR' 2 (by decide)) (pR' 1 (by decide))]
    exact cmC
  have h10 : allLt p1Gens.size (fun k => cmA 24 p1Gens[k]! r2Arr) = true := by
    refine allLt_iff.2 fun k hk => ?_
    rw [gP1.1] at hk
    rw [gP1.2 k hk, hr2, cmA_unpack sz5 (allR pP1 k hk) (pR' 1 (by decide))]
    exact allR cmP1 k hk
  unfold hatM24Check
  rw [h1, eS1.1, eS1.2.1, h4, h5, h6, h7, eP1.1, eP1.2.1, h10, eP2.1, eP2.2.1, coverOK_true]
  rfl

end CertificateChecks.KernelHatM

end
