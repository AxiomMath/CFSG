
module

public import Certificates.Kernel.OmegaEight.SA3002KC
public import Certificates.Kernel.OmegaEight.SA3002KF
public import Certificates.Kernel.OmegaEight.SA3002KI
public import Certificates.Kernel.OmegaEight.SA3002KR
public import Certificates.Kernel.OmegaEight.Bridge3009
public import CFSG.Certificates.Kernel.O8SAMSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowBase
public import Certificates.Certificate3009Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight (matMulM idCode wordsOf)
open CFSG.KC.BfsPin (compA_unpack invCand_unpack canonK_pcomp eqA_unpack)
open CFSG.KLC.E8 (strictB_eq')
open CFSG.KC.Misc.PairCount (unpack_get)

theorem saMat_eqM (i : Nat) : saMat i = saAtK saCodes i := (saAtK_eq _ _).symm
theorem saGen_eqM (l : Nat) : saGen l = ix13 saGenT l := (ix13_eq _ _).symm
theorem saMul_eqM (i l : Nat) : saMul i l = ix13 saMulT (Nat.add (Nat.mul 6 i) l) :=
  (ix13_eq _ _).symm
theorem saPar_eqM (i : Nat) : saPar i = ix13 saParT i := (ix13_eq _ _).symm
theorem saLab_eqM (i : Nat) : saLab i = Nat.land (Nat.shiftRight saLabT (Nat.mul 3 i)) 7 :=
  (fld_eq saLabT (3 * i) 3).symm
theorem yIdx_eqM (j : Nat) : yIdx j = ix13 yIdxT j := (ix13_eq _ _).symm
theorem rgCode_eqM (j l : Nat) : rgCode j l = saAtK rgT (Nat.add (Nat.mul 5 j) l) :=
  (saAtK_eq _ _).symm
theorem rgInv_eqM (j l : Nat) : rgInv j l = saAtK rgInvT (Nat.add (Nat.mul 5 j) l) :=
  (saAtK_eq _ _).symm

theorem invW_eqM (i : Nat) : invW i =
    (Nat.land (Nat.shiftRight invWT (Nat.add (Nat.mul 32 i) 26)) 63,
      Nat.land (Nat.shiftRight invWT (Nat.add (Nat.mul 32 i) 13)) 8191,
      Nat.land (Nat.shiftRight invWT (Nat.mul 32 i)) 8191) :=
  Prod.ext (fld_eq invWT (32 * i + 26) 6).symm
    (Prod.ext (fld_eq invWT (32 * i + 13) 13).symm (fld_eq invWT (32 * i) 13).symm)

theorem ns_bindM : ∀ p < 136, nsArr[p]! = pg 8 255 NSM p := by decide +kernel

theorem ni_bindM : ∀ v < 256, nsIdx[v]! = pg 8 255 NIM v := by decide +kernel

theorem wordEqK_ofM {S SI : Nat → Nat} {kS : Nat} {wd : List Int} (h : lettersK kS wd = true) :
    wordEqK 136 8 (mask 8) (pidn 136 8) S SI kS wd (wordK 136 8 (mask 8) (pidn 136 8) S SI wd) =
      true := by
  unfold wordEqK
  rw [h, Nat.beq_refl]
  rfl

theorem genM_get {j : Nat} (hj : j < 11) : genArrs[j]! = unpack 136 8 (AM.S j) := genAM.2 j hj

theorem omegaGensM : (genArrs.extract 0 10).size = 10 ∧
    ∀ j < 10, (genArrs.extract 0 10)[j]! = unpack 136 8 (OmM.S j) := by
  refine ⟨by simp [genAM.1], fun j hj => ?_⟩
  have e : (genArrs.extract 0 10)[j]! = genArrs[j]! := by
    rw [getElem!_pos _ j (by simp [genAM.1]; omega), getElem!_pos _ j (by rw [genAM.1]; omega)]
    simp
  rw [e, genM_get (by omega), Nat.eq_of_beq_eq_true (allN_spec kGenOmM j hj)]

theorem autGensM : genArrs.size = 11 ∧ ∀ j < 11, genArrs[j]! = unpack 136 8 (AQM.S j) :=
  ⟨genAM.1, fun j hj => by rw [genM_get hj, Nat.eq_of_beq_eq_true (allN_spec kGenAQM j hj)]⟩

theorem sylowGensM : sylowGens.size = 6 ∧ ∀ j < 6, sylowGens[j]! = unpack 136 8 (SYM.S j) := by
  refine ⟨sylowGens_size, fun j hj => ?_⟩
  rw [sylowGens_getElem! hj, genM_get (sylowIdx_lt hj),
    Nat.eq_of_beq_eq_true (allN_spec kGenSYM j hj)]

theorem omegaS_bindM : omegaS.size = 18 ∧ ∀ j < 18, omegaS[j]! = unpack 136 8 (OmM.S j) :=
  pushWords_eq omegaGensM OmM.head

theorem autS_bindM : autS.size = 19 ∧ ∀ j < 19, autS[j]! = unpack 136 8 (AQM.S j) :=
  pushWords_eq autGensM AQM.head

theorem sylowS_bindM : sylowS.size = 9 ∧ ∀ j < 9, sylowS[j]! = unpack 136 8 (SYM.S j) :=
  pushWords_eq sylowGensM SYM.head

theorem bindsOmM : Binds 136 8 OmM.S 18 7 OmM.BP omegaS ((omegaBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, omegaS_bindM.1, omegaS_bindM.2, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem bindsAQM : Binds 136 8 AQM.S 19 8 AQM.BP autS ((autBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, autS_bindM.1, autS_bindM.2, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem bindsSYM : Binds 136 8 SYM.S 9 5 SYM.BP sylowS ((sylowBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, sylowS_bindM.1, sylowS_bindM.2, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem sylowW_eqM {wd : List Int} (h : lettersK 9 wd = true) : sylowW wd = unpack 136 8 (wSM wd) :=
  (wordEqK_sound sylowS_bindM (perm_of_head SYM.head) (wordEqK_ofM h)).1

theorem autW_eqM {wd : List Int} (h : lettersK 19 wd = true) : autW wd = unpack 136 8 (wAM wd) :=
  (wordEqK_sound autS_bindM (perm_of_head AQM.head) (wordEqK_ofM h)).1

theorem omegaW_eqM {wd : List Int} (h : lettersK 18 wd = true) : omegaW wd = unpack 136 8 (wOM wd) :=
  (wordEqK_sound omegaS_bindM (perm_of_head OmM.head) (wordEqK_ofM h)).1

theorem omegaChain_kM : omegaChainCheck = true := by
  unfold omegaChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsOmM OmM.head OmM.hl (by decide) OmM.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsOmM (perm_of_head OmM.head) OmM.hl]
  decide +kernel

theorem autChain_kM : autChainCheck = true := by
  unfold autChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsAQM AQM.head AQM.hl (by decide) AQM.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsAQM (perm_of_head AQM.head) AQM.hl]
  decide +kernel

theorem sylowChain_kM : sylowChainCheck = true := by
  unfold sylowChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsSYM SYM.head SYM.hl (by decide) SYM.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsSYM (perm_of_head SYM.head) SYM.hl]
  decide +kernel

theorem at8_eq {P p : Nat} (hp : p < 136) : (unpack 136 8 P)[p]! = at8 P p := unpack_get hp

theorem compA_pcM {p q : Nat} (hp : cnM p = true) (hq : cnM q = true) :
    compA 136 (unpack 136 8 p) (unpack 136 8 q) = unpack 136 8 (pcM p q) := compA_unpack hp hq

theorem cn_pcM {p q : Nat} (hp : cnM p = true) (hq : cnM q = true) : cnM (pcM p q) = true :=
  canonK_pcomp hp hq

theorem invCand_pinvM {p : Nat} (h : pmM p = true) :
    invCand 136 (unpack 136 8 p) = unpack 136 8 (pinvM p) := invCand_unpack h

theorem eqA_pcM {p q : Nat} (hp : cnM p = true) (hq : cnM q = true) :
    eqA 136 (unpack 136 8 p) (unpack 136 8 q) = Nat.beq p q := eqA_unpack hp hq

theorem conjArr_cjM {c x : Nat} (hc : cnM c = true) (hci : cnM (pinvM c) = true)
    (hp : pmM c = true) (hx : cnM x = true) :
    conjArr (unpack 136 8 c) (unpack 136 8 x) = unpack 136 8 (cjM c x) := by
  unfold conjArr
  rw [invCand_pinvM hp, compA_pcM hc hx, compA_pcM (cn_pcM hc hx) hci]
  rfl

theorem cn_cjM {c x : Nat} (hc : cnM c = true) (hci : cnM (pinvM c) = true) (hx : cnM x = true) :
    cnM (cjM c x) = true := cn_pcM (cn_pcM hc hx) hci

theorem kPidM' : cnM pidM = true ∧ CFSG.KS.Prim.idK 136 8 (mask 8) = true := (bAnd_iff _ _).1 kPidM

theorem idA_eqM : idA 136 = unpack 136 8 pidM := (idK_sound kPidM'.2).symm

theorem commArr_pcM {p q : Nat} (hp : cnM p = true) (hq : cnM q = true) :
    commArr (unpack 136 8 p) (unpack 136 8 q) = Nat.beq (pcM p q) (pcM q p) := by
  unfold commArr
  rw [compA_pcM hp hq, compA_pcM hq hp, eqA_pcM (cn_pcM hp hq) (cn_pcM hq hp)]

theorem isInvA_ofM {p : Nat} (h : pmM p = true) :
    isInvA 136 (unpack 136 8 p) (invCand 136 (unpack 136 8 p)) = true := by
  have := invEqK_sound h
  rw [this.1]
  exact this.2

theorem powArr_eqM (t : Array ℕ) : ∀ k, powArr t k = CFSG.Sporadic.Schreier.Co3.co3PowA 136 t k
  | 0 => rfl
  | k + 1 => by rw [powArr, powArr_eqM t k]; rfl

theorem powArr_pcM {p : Nat} (hp : cnM p = true) (k : Nat) :
    powArr (unpack 136 8 p) k = unpack 136 8 (ppwM p k) := by
  rw [powArr_eqM]
  exact powEqK_sound ((bAnd_iff _ _).2 ⟨hp, Nat.beq_refl _⟩)

theorem rgLen_eqM : ∀ j < 36, rgLenM j = 3 ∨ rgLenM j = 4 := by decide

theorem repGens_lengthM {j : Nat} : (repGens j).length = rgLenM j + 1 := by
  rw [repGens, List.length_append, List.length_map]
  rfl

theorem repArrs_getM {j : Nat} (hj : j < 36) (h : lettersK 9 (repWords.getD j []) = true) :
    repArrs.getD j #[] = unpack 136 8 (wSM (repWords.getD j [])) := by
  rw [repArrs, getD_map_of_lt sylowW [] #[] (by simp [repWords]; omega), sylowW_eqM h]

theorem rgJ_okM : ∀ j < 36, rgJM j = true :=
  forall_of_blocks (B := 8) (k := 4) (fun s hs => by
    interval_cases s
    exacts [kRgM0, kRgM1, kRgM2, kRgM3]) kRgM4

theorem fiveJ_okM : ∀ j < 36, fiveJM j = true :=
  forall_of_blocks (B := 4) (k := 9) (r := 0) (fun s hs => by
    interval_cases s
    exacts [kFiveM0, kFiveM1, kFiveM2, kFiveM3, kFiveM4, kFiveM5, kFiveM6, kFiveM7, kFiveM8]) rfl

theorem closed_okM : ∀ i < 8192, saClosedAtG 6 saCodes saMulT saGenT i = true :=
  forall_of_blocks (B := 1024) (k := 8) (r := 0) (fun s hs => by
    interval_cases s
    exacts [kClosedM0, kClosedM1, kClosedM2, kClosedM3, kClosedM4, kClosedM5, kClosedM6,
      kClosedM7]) rfl

theorem invol_okM : ∀ i < 8192, involAtG 36 saCodes yIdxT invWT i = true :=
  forall_of_blocks (B := 2048) (k := 4) (r := 0) (fun s hs => by
    interval_cases s
    exacts [kInvolM0, kInvolM1, kInvolM2, kInvolM3]) rfl

theorem repGens_getM {j l : Nat} (hj : j < 36) (hl : l ≤ rgLenM j) :
    (repGens j).getD l #[] = unpack 136 8 (rgKM j l) ∧ rgOKM j l = true := by
  have hl5 : l < 5 := by rcases rgLen_eqM j hj with h | h <;> omega
  have hr := allN_spec (rgJ_okM j hj) l hl5
  rw [ble_true hl] at hr
  refine ⟨?_, hr⟩
  unfold rgOKM at hr
  simp only [bAnd_iff] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hr
  have e1 : (cent0Words.getD (repTypes.getD j 0) []).length = rgLenM j := rfl
  rcases Nat.lt_or_ge l (rgLenM j) with h | h
  · rw [repGens, List.getD_append _ _ _ _ (by rw [List.length_map, e1]; exact h),
      getD_map_of_lt _ [] #[] (by rw [e1]; exact h),
      conjArrs, getD_map_of_lt autW [] #[] (by simp [conjWords]; omega), autW_eqM h1,
      omegaW_eqM h2, conjArr_cjM h3 h4 h5 h6]
    unfold rgKM
    rw [blt_true h]
  · have hl4 : l = rgLenM j := by omega
    subst hl4
    have hk := allN_spec kRepsM j hj
    simp only [bAnd_iff] at hk
    rw [repGens, List.getD_append_right _ _ _ _ (by rw [List.length_map, e1]), List.length_map, e1,
      Nat.sub_self, List.getD_cons_zero, repArrs_getM hj hk.2.1]
    have hb : Nat.blt (rgLenM j) (rgLenM j) = false :=
      Bool.eq_false_iff.2 fun h => Nat.lt_irrefl _ (of_blt h)
    unfold rgKM
    rw [hb]

theorem acts_ofM {P M : Nat} (h : actsMK NSM NIM P M = true) : ActsOn (unpack 136 8 P) M :=
  actsMK_sound ns_bindM ni_bindM h

theorem cwK_letters (k : Nat) : ∀ v ∈ cwK k, ∀ l ∈ v, l < k := by
  intro v hv l hl
  simp only [cwK, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.mem_range, List.not_mem_nil, or_false] at hv
  rcases hv with ((rfl | ⟨a, ha, rfl⟩) | ⟨a, ha, b, hb, rfl⟩) | ⟨a, ha, b, hb, c, hc, rfl⟩ <;>
    simp_all <;> omega

theorem sa_facts_kM : SAFacts where
  gens l hl := by
    have h := allN_spec kGensM l hl
    simp only [bAnd_iff, Nat.blt_eq] at h
    rw [saGen_eqM, saMat_eqM, sylowGens_getElem! hl, genM_get (sylowIdx_lt hl)]
    exact ⟨h.1, acts_ofM h.2⟩
  id0 := by rw [saMat_eqM, Nat.eq_of_beq_eq_true kIdM, idK_eq]
  closed i hi l hl := by
    have h := closed_okM i hi
    unfold saClosedAtG at h
    simp only [strictB_eq'] at h
    have h2 := Nat.eq_of_beq_eq_true (allN_spec h l hl)
    rw [matMulK_eq] at h2
    simp only [saMat_eqM, saGen_eqM, saMul_eqM]
    exact h2
  tree i hi h0 := by
    have h := allN_spec kTreeM i hi
    unfold saTreeAtG at h
    rw [beq_false (by omega : i ≠ 0)] at h
    simp only [strictB_eq', bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
    rw [saPar_eqM, saLab_eqM, saMul_eqM]
    exact h
  distinct i hi k hk e := by
    have hs : ∀ a < 8192, ix13 saSPIM a < 8192 ∧ ix13 saSPM (ix13 saSPIM a) = a ∧
        (a < 8191 → saAtK saCodes (ix13 saSPM a) < saAtK saCodes (ix13 saSPM (a + 1))) := by
      intro a ha
      have h := allN_spec kSortM a ha
      unfold saSortAt at h
      simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
      refine ⟨h.1, h.2.1, fun h' => ?_⟩
      have h3 := h.2.2
      rw [blt_true h'] at h3
      exact of_blt h3
    have hm := sorted_mono (f := fun a => saAtK saCodes (ix13 saSPM a))
      fun a ha => (hs a (by omega)).2.2 ha
    obtain ⟨hi1, hi2, -⟩ := hs i hi
    obtain ⟨hk1, hk2, -⟩ := hs k hk
    rw [saMat_eqM, saMat_eqM, ← hi2, ← hk2] at e
    rcases Nat.lt_trichotomy (ix13 saSPIM i) (ix13 saSPIM k) with h | h | h
    · exact absurd e (Nat.ne_of_lt (hm _ hk1 _ h))
    · rw [← hi2, ← hk2, h]
    · exact absurd e (Nat.ne_of_gt (hm _ hi1 _ h))
  span := by decide +kernel
  reps j hj := by
    have h := allN_spec kRepsM j hj
    simp only [bAnd_iff] at h
    rw [yIdx_eqM, saMat_eqM, repArrs_getM hj h.2.1]
    exact ⟨of_blt h.1, acts_ofM h.2.2.2⟩
  invol i hi h0 hsq := by
    have h := invol_okM i hi
    unfold involAtG at h
    rw [saMat_eqM, ← matMulK_eq, ← idK_eq] at hsq
    simp only [strictB_eq'] at h
    rw [beq_false h0, beq_true hsq] at h
    simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [invW_eqM]
    simp only [saMat_eqM, yIdx_eqM, ← matMulK_eq, ← idK_eq]
    exact ⟨h1, h2, h3, h4, h5⟩
  rg j hj l hl := by
    rw [repGens_lengthM] at hl
    obtain ⟨e, h⟩ := repGens_getM (l := l) hj (by omega)
    unfold rgOKM at h
    simp only [bAnd_iff] at h
    rw [e, invCand_pinvM h.2.2.2.2.2.2.2.1, rgCode_eqM, rgInv_eqM]
    exact ⟨acts_ofM h.2.2.2.2.2.2.2.2.1, acts_ofM h.2.2.2.2.2.2.2.2.2⟩
  five j hj i hi h1 h2 h3 := by
    have h := allN_spec (fiveJ_okM j hj) i hi
    unfold fiveAt at h
    simp only [saMat_eqM, yIdx_eqM, ← matMulK_eq, ← idK_eq] at h1 h2 h3
    simp only [strictB_eq'] at h
    rw [beq_false h1, beq_true h2, beq_true h3] at h
    simp only at h
    obtain ⟨vs, hl, hm, hp⟩ := greedyK_sound _ _ _ _ [] [] rfl List.Pairwise.nil h
    have eG : (fun l => saAtK rgT (Nat.add (Nat.mul 5 j) l)) = rgCode j :=
      funext fun l => (rgCode_eqM j l).symm
    have eGi : (fun l => saAtK rgInvT (Nat.add (Nat.mul 5 j) l)) = rgInv j :=
      funext fun l => (rgInv_eqM j l).symm
    rw [eG, eGi] at hp
    refine ⟨vs, hl, fun v hv l hl' => ?_, ?_⟩
    · rw [repGens_lengthM]
      rcases hm v hv with h' | h'
      · exact absurd h' List.not_mem_nil
      · exact cwK_letters _ v h' l hl'
    · simpa [rgConj, saMat_eqM] using hp

theorem mainArrs_getM {i : Nat} (hi : i < 5) (h : lettersK 9 (mainWords.getD i []) = true) :
    mainArrs.getD i #[] = unpack 136 8 (mainKM i) := by
  rw [mainArrs, getD_map_of_lt sylowW [] #[] (by simp [mainWords]; omega), sylowW_eqM h]
  rfl

theorem main_okM {i : Nat} (hi : i < 5) :
    mainArrs.getD i #[] = unpack 136 8 (mainKM i) ∧ cnM (mainKM i) = true ∧ pmM (mainKM i) = true := by
  have h := allN_spec kMainM i hi
  simp only [bAnd_iff] at h
  exact ⟨mainArrs_getM hi h.1, h.2.1, h.2.2⟩

theorem conjArrs_getM {j : Nat} (hj : j < 36) (h : lettersK 19 (conjWords.getD j []) = true) :
    conjArrs.getD j #[] = unpack 136 8 (wAM (conjWords.getD j [])) := by
  rw [conjArrs, getD_map_of_lt autW [] #[] (by simp [conjWords]; omega), autW_eqM h]

theorem structure_kM : structureCheck = true := by
  have hC := kStrCM
  simp only [bAnd_iff] at hC
  obtain ⟨hc, h10, hi10⟩ := hC
  have hc' : ∀ j < 11, cnM (AM.S j) = true := allN_spec hc
  unfold structureCheck
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have h := allN_spec kStrM i hi
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨hr, e1⟩ := h
  rw [genM_get (by omega : 10 < 11), genM_get (by omega : i < 11), genM_get (by omega),
    conjArr_cjM (hc' 10 (by omega)) hi10 h10 (hc' i (by omega)),
    eqA_pcM (cn_cjM (hc' 10 (by omega)) hi10 (hc' i (by omega))) (hc' _ (by omega)), e1]

theorem stab_kM : CFSG.EvenSmallLie.OmegaEightMinus.stabCheck = true := by
  unfold CFSG.EvenSmallLie.OmegaEightMinus.stabCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun j hj => ?_, fun p hp => ?_⟩
  · have h := List.all_eq_true.1 kStabM1 j hj
    simp only [bAnd_iff, Nat.blt_eq] at h
    rw [omegaS_bindM.1, omegaS_bindM.2 j h.1, at8_eq (p := 0) (by norm_num)]
    simp [h.1, Nat.eq_of_beq_eq_true h.2]
  · rw [List.mem_range] at hp
    have h := allN_spec kStabM2 p hp
    rw [List.any_eq_true] at h ⊢
    obtain ⟨j, hj, hne⟩ := h
    have hj18 := of_blt ((bAnd_iff _ _).1 (List.all_eq_true.1 kStabM1 j hj)).1
    refine ⟨j, hj, ?_⟩
    rw [omegaS_bindM.2 j hj18, at8_eq (p := p + 1) (by omega)]
    exact bne_of hne

theorem tree_kM : treeLitCheck = true := by
  have hm : (treeLit.2.2[0]! == 0) = true ∧ ∀ i < 135, treeLit.1[i + 1]! < 136 ∧
      treeLit.2.1[i + 1]! < 10 ∧ treeLit.2.2[treeLit.1[i + 1]!]! < treeLit.2.2[i + 1]! := by
    decide +kernel
  unfold treeLitCheck treeOK
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨hm.1, fun i hi => ?_⟩
  rw [List.mem_range] at hi
  obtain ⟨h1, h2, h3⟩ := hm.2 i hi
  rw [genM_get (lt_of_lt_of_le h2 (by norm_num)), at8_eq h1]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec kTreeGM i hi))⟩

theorem repArrs_memM {r : Array ℕ} (hr : r ∈ repArrs) : ∃ j < 36, repArrs.getD j #[] = r := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hr
  have hl : repArrs.length = 36 := by simp [repArrs, repWords]
  refine ⟨j, hl ▸ hj, ?_⟩
  rw [List.getD_eq_getElem _ _ hj, e]

theorem rep_okM {j : Nat} (hj : j < 36) :
    repArrs.getD j #[] = unpack 136 8 (wSM (repWords.getD j [])) ∧
      cnM (wSM (repWords.getD j [])) = true := by
  have hk := allN_spec kRepsM j hj
  simp only [bAnd_iff] at hk
  exact ⟨repArrs_getM hj hk.2.1, hk.2.2.1⟩

theorem conj_okM {j : Nat} (hj : j < 36) : lettersK 19 (conjWords.getD j []) = true ∧
    cnM (wAM (conjWords.getD j [])) = true ∧ cnM (pinvM (wAM (conjWords.getD j []))) = true ∧
    pmM (wAM (conjWords.getD j [])) = true := by
  have hg := (repGens_getM hj (Nat.zero_le _)).2
  unfold rgOKM at hg
  simp only [bAnd_iff] at hg
  exact ⟨hg.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1⟩

theorem sylowReps_kM : sylowRepsLitCheck = true := by
  unfold sylowRepsLitCheck
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun r hr => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := repArrs_memM hr
    have h := allN_spec kSylowRepsM j hj
    simp only [bAnd_iff] at h
    obtain ⟨e, hcn⟩ := rep_okM hj
    rw [e, CFSG.KC.Child3.ordTest2_unpack hcn, Bool.and_eq_true]
    exact ⟨h.2.2.1, not_beq_of h.2.2.2.1⟩
  · rw [List.mem_range] at hj
    have h := allN_spec kSylowRepsM j hj
    simp only [bAnd_iff] at h
    obtain ⟨hcn, hpm, hsq, hne, hsift, ht5, hconj⟩ := h
    obtain ⟨e, -⟩ := rep_okM hj
    obtain ⟨hl1, hc1, hc2, hc3⟩ := conj_okM hj
    obtain ⟨em, hmc, -⟩ := main_okM (of_blt ht5)
    have hG : Nat.shiftRight (wSM (repWords.getD j [])) (136 * 8) = 0 := by
      unfold cnM canonK at hcn
      simp only [bAnd_iff] at hcn
      exact Nat.eq_of_beq_eq_true hcn.2.1
    rw [e, conjArrs_getM hj hl1, em, conjArr_cjM hc1 hc2 hc3 hmc,
      eqA_pcM (cn_cjM hc1 hc2 hmc) hcn, Nat.eq_of_beq_eq_true hconj, Nat.beq_refl, Bool.and_true,
      siftK_eq bindsOmM (perm_of_head OmM.head) OmM.hl rfl hG (range_of_permOK hpm)]
    have h3 : decide (repTypes.getD j 0 < 3) = Nat.blt (repTypes.getD j 0) 3 := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
    rw [h3]
    revert hsift
    cases siftK 136 8 (mask 8) (136 * 8) (pidn 136 8) OmM.LR OmM.TRI OmM.BP 7 0 (wSM (repWords.getD j [])) <;>
      cases Nat.blt (repTypes.getD j 0) 3 <;> decide

theorem cent0_kM : cent0Check = true := by
  unfold cent0Check
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [List.all_eq_true]
  intro wd hw
  have h := List.all_eq_true.1 (allN_spec kCentM i hi) wd hw
  simp only [bAnd_iff] at h
  obtain ⟨em, hmc, -⟩ := main_okM hi
  rw [omegaW_eqM h.1, em, commArr_pcM h.2.1 hmc]
  exact h.2.2.2

theorem fg_kM : fgCheck = true := by
  unfold fgCheck
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have h := allN_spec kFgM i hi
  simp only [bAnd_iff, strictB_eq'] at h
  obtain ⟨hl, hc, hci, hp, hsq, hne⟩ := h
  obtain ⟨em, hmc, -⟩ := main_okM (by omega : i + 3 < 5)
  simp only
  rw [em, omegaW_eqM hl, conjArr_cjM hc hci hp hmc, compA_pcM (cn_cjM hc hci hmc) hmc,
    compA_pcM (cn_pcM (cn_cjM hc hci hmc) hmc) (cn_pcM (cn_cjM hc hci hmc) hmc), idA_eqM,
    eqA_pcM (cn_pcM (cn_pcM (cn_cjM hc hci hmc) hmc) (cn_pcM (cn_cjM hc hci hmc) hmc)) kPidM'.1,
    eqA_pcM (cn_pcM (cn_cjM hc hci hmc) hmc) kPidM'.1, Bool.and_eq_true]
  exact ⟨hsq, not_beq_of hne⟩

theorem odd_kM : oddCheck = true := by
  unfold oddCheck
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have h := allN_spec kOddM i hi
  simp only [bAnd_iff, strictB_eq'] at h
  obtain ⟨hl1, hl2, hu, hv, hou, hov, hcu, hcv, hpow⟩ := h
  obtain ⟨em, hmc, -⟩ := main_okM (by omega : i < 5)
  have hpar : ∀ k < 3, (oddData.getD k ([], [], 0, 0, 0)).2.2.2.1 % 2 = 1 ∧
      (oddData.getD k ([], [], 0, 0, 0)).2.2.2.2 % 2 = 1 := by decide
  obtain ⟨hp1, hp2⟩ := hpar i hi
  simp only
  rw [em, omegaW_eqM hl1, omegaW_eqM hl2, CFSG.KC.O8.ordK_sound hu hou, CFSG.KC.O8.ordK_sound hv hov,
    commArr_pcM hu hmc, commArr_pcM hv hmc, hcu, hcv, compA_pcM hu hv, powArr_pcM (cn_pcM hu hv),
    Nat.eq_of_beq_eq_true hpow, eqA_pcM hmc hmc, Nat.beq_refl]
  simp only [hp1, hp2, beq_self_eq_true, Bool.and_self]

theorem invs_kM : invsCheck = true := by
  unfold invsCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_append]
  refine ⟨⟨⟨fun j hj t ht => ?_, fun t ht => ?_⟩, fun ws hws w hw => ?_⟩, fun w hw => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 ht
    have hl' : l ≤ rgLenM j := by
      rw [repGens_lengthM] at hl
      omega
    obtain ⟨e, h⟩ := repGens_getM hj hl'
    rw [← List.getD_eq_getElem _ #[] hl, e]
    unfold rgOKM at h
    simp only [bAnd_iff] at h
    exact isInvA_ofM h.2.2.2.2.2.2.2.1
  · rcases ht with (ht | ht) | ht
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ht
      have hl : conjArrs.length = 36 := by simp [conjArrs, conjWords]
      have hj' : j < 36 := hl ▸ hj
      obtain ⟨hl1, -, -, hp⟩ := conj_okM hj'
      rw [← List.getD_eq_getElem _ #[] hj, conjArrs_getM hj' hl1]
      exact isInvA_ofM hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
      have hl : mainArrs.length = 5 := by simp [mainArrs, mainWords]
      obtain ⟨em, -, hp⟩ := main_okM (hl ▸ hi)
      rw [← List.getD_eq_getElem _ #[] hi, em]
      exact isInvA_ofM hp
    · obtain ⟨j, hj, rfl⟩ := repArrs_memM ht
      have h := allN_spec kSylowRepsM j hj
      simp only [bAnd_iff] at h
      rw [(rep_okM hj).1]
      exact isInvA_ofM h.2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hws
    have hl : cent0Words.length = 5 := by simp [cent0Words]
    have h := List.all_eq_true.1 (allN_spec kCentM i (hl ▸ hi)) w
      (by rwa [List.getD_eq_getElem _ [] hi])
    simp only [bAnd_iff] at h
    rw [omegaW_eqM h.1]
    exact isInvA_ofM h.2.2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have hl : fgWords.length = 2 := by simp [fgWords]
    have h := allN_spec kFgM i (hl ▸ hi)
    simp only [bAnd_iff] at h
    rw [← List.getD_eq_getElem _ [] hi, omegaW_eqM h.1]
    exact isInvA_ofM h.2.2.2.1

open Certificates in
open CFSG.EvenSmallLie.OmegaEightMinus in
theorem cert3002 : (CFSG.EvenSmallLie.OmegaEightMinus.nsCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.omegaChainCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.autChainCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.sylowChainCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.structureCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.stabCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.treeLitCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.sylowRepsLitCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.cent0Check = true)
    ∧ SAFacts
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.fgCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.oddCheck = true)
    ∧ (CFSG.EvenSmallLie.OmegaEightMinus.invsCheck = true) :=
  ⟨by decide +kernel, omegaChain_kM, autChain_kM, sylowChain_kM, structure_kM, stab_kM, tree_kM,
    sylowReps_kM, cent0_kM, sa_facts_kM, fg_kM, odd_kM, invs_kM⟩

end CertificateChecks.KernelO8

end
