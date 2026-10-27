module

public import Certificates.Kernel.Sporadic.ON8.Lin
public import Certificates.Kernel.Sporadic.ON8.ChecksD
public import Certificates.Kernel.Sporadic.ON8.ChecksH
public import Certificates.Kernel.Sporadic.ON8.ChecksS
public import Certificates.Kernel.Sporadic.ON3.Final
public import Certificates.Kernel.Sporadic.ON5.Final
public import CFSG.Certificates.Kernel.Spor.ChainKProof
public import CFSG.Sporadic.Schreier.ONCheckR3EInputs
public meta import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON8.Neg
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON8.dAll CertificateChecks.KernelSpor.ON8.dSl 9
#kon_join CertificateChecks.KernelSpor.ON8.aAll CertificateChecks.KernelSpor.ON8.aSl 9
#kon_join CertificateChecks.KernelSpor.ON8.hAll CertificateChecks.KernelSpor.ON8.hSl 9
#kon_join CertificateChecks.KernelSpor.ON8.tAll CertificateChecks.KernelSpor.ON8.tSl 9
#kon_join CertificateChecks.KernelSpor.ON8.mAll CertificateChecks.KernelSpor.ON8.mSel 20

namespace CertificateChecks.KernelSpor.ON8

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONLin CFSG.KS.IE CFSG.KS.TW CFSG.KS.PW
  CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BfsReplay
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor.ON3 (ZT QT CT CIT DT M2T M3T mG trW tab_facts word_pair c_CI
  z_get q_get c_get ci_get m_get dConj_get qPow_get peq_of' peq_false_of' bB
  blockTab_of bposK blkK)
open CertificateChecks.KernelSpor.ON5K (all_comm comp_unpackG pisInv_of blocks_eq)

theorem lt_of_L {F : Nat → Nat} (h : L F) {x : Nat} (hx : x < 245520) : F x < 245520 := by
  obtain ⟨M, hM⟩ := h
  exact (hM x hx).1

theorem rel_parts : (∀ j < 5, ∀ x < 245520, dhI j (dhG j x) = x) ∧
    (∀ j < 3, ∀ x < 245520, mwK j x = mG j x) ∧
    (∀ x < 245520, Nat.rec (motive := fun _ => Nat) x (fun _ acc => M2T acc) 7 = x) ∧
    (∀ x < 245520, vK (vK x) = x) ∧
    (∀ j < 4, ∀ x < 245520, vK (dcK j x) = dcK j (vK x)) ∧
    (∀ x < 245520, ZT x = QT (QT x)) ∧
    (∀ i < 4, ∀ a < 4, onP (fun x => hGK i (eD (asl a) x)) (fun x => eD (asl a) (hGK i x)) = true) := by
  have h := rel_ok
  unfold relOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hpow : L fun x => Nat.rec (motive := fun _ => Nat) x (fun _ acc => M2T acc) 7 := by
    have : ∀ k, L fun x => Nat.rec (motive := fun _ => Nat) x (fun _ acc => M2T acc) k := by
      intro k
      induction k with
      | zero => exact Lin.id
      | succ k ih => exact Lin.comp lin_M2T ih
    exact this 7
  refine ⟨fun j hj => agree (Lin.comp (lin_dhI) (lin_dhG)) Lin.id (allN_spec h1 j hj),
    fun j hj => agree (lin_wDH (k := 5 + j) (by omega)) (lin_mG hj) (allN_spec h2 j hj),
    agree hpow Lin.id h3, agree (Lin.comp lin_vK lin_vK) Lin.id h4,
    fun j hj => agree (Lin.comp lin_vK (lin_dcK hj)) (Lin.comp (lin_dcK hj) lin_vK) (allN_spec h5 j hj),
    agree lin_ZT (Lin.comp lin_QT lin_QT) h6,
    fun i hi a ha => allN_spec (allN_spec h7 i hi) a ha⟩

theorem memM' {g : Array Nat} {G : Nat → Nat} (hg : ∀ k < 3, g[bB k]! = G (bB k))
    (hG : ∀ k < 3, G (bB k) < 245520)
    (hs : CertificateChecks.KernelSpor.ON3.siftM G = true) : memIn MStrong Data.MChain.base g = true := by
  unfold memIn
  exact CFSG.KS.CH.memIn3_proved (B := bB) (G := fun k => G (bB k)) CertificateChecks.KernelSpor.ON3.mStrong_get.1
    (fun j hj => by rw [CertificateChecks.KernelSpor.ON3.mStrong_get.2 j hj, Array.size_ofFn])
    (CertificateChecks.KernelSpor.ON3.strong_facts CertificateChecks.KernelSpor.ON3.mStrong_get CertificateChecks.KernelSpor.ON3.mF_pair) CertificateChecks.KernelSpor.ON3.base_facts.1 CertificateChecks.KernelSpor.ON3.base_facts.2 hg hG (by decide)
    (fun i hi => (CertificateChecks.KernelSpor.ON3.heads hi).2.1) (fun i hi => (CertificateChecks.KernelSpor.ON3.heads hi).2.2.2.2.1)
    (fun i hi => CertificateChecks.KernelSpor.ON3.ptM_all hi) (fun i hi => CertificateChecks.KernelSpor.ON3.posM_all hi) hs

theorem hArr_get : ∀ x < 245520, hArr[x]! = M2T x ∧ M2T x < 245520 :=
  m_get (j := 1) (by norm_num)

theorem hArr_size : hArr.size = nPts := by
  unfold hArr
  rw [CertificateChecks.KernelSpor.ON3.wordArrs_get (by decide)]
  exact pword_size _

theorem hinv_get : ∀ x < 245520, (pinvCand nPts hArr)[x]! = hIK x := by
  intro x hx
  rw [arr_ext hArr_size fun y hy => (hArr_get y hy).1]
  refine CFSG.KS.CB.pinvCand_get (fun y hy => (hArr_get y hy).2) (fun y hy => ?_) hx
  rw [(tab_facts hy).2.2.2.2.2.2.2.2.1]
  exact (word_pair (k := 7) (by norm_num) y hy).2.2.1

theorem dConj_size : dConj.size = 4 := by
  unfold dConj
  rw [Array.size_map, wordArrs, pwords_eq, Array.size_map]
  rfl

theorem dhGens_lo {j : Nat} (h4 : j < 4) : dhGens[j]! = dConj[j]! := by
  unfold dhGens
  rw [getElem!_pos _ j (by simp [dConj_size]; omega), Array.getElem_push_lt (by rw [dConj_size]; exact h4),
    ← getElem!_pos dConj j (by rw [dConj_size]; exact h4)]

theorem dhGens_four : dhGens[4]! = hArr := by
  unfold dhGens
  have e : (4 : Nat) = dConj.size := by rw [dConj_size]
  rw [getElem!_pos _ 4 (by simp [dConj_size]), Array.getElem_push]
  simp [dConj_size]

theorem dhGens_get {j : Nat} (hj : j < 5) {x : Nat} (hx : x < 245520) :
    (dhGens[j]!)[x]! = dhG j x := by
  by_cases h4 : j < 4
  · rw [dhGens_lo h4, (dConj_get h4 hx).1, dhG, nIf_lt h4]
    rfl
  · have e : j = 4 := by omega
    subst e
    rw [dhGens_four, (hArr_get x hx).1]
    rfl

theorem dConj_szj {j : Nat} (hj : j < 4) : (dConj[j]!).size = nPts := by
  unfold dConj
  rw [getElem!_pos _ j (by simp [wordArrs, pwords_eq]; exact hj), Array.getElem_map]
  simp [Native.pcomp]

theorem dhGens_size' {j : Nat} (hj : j < 5) : (dhGens[j]!).size = nPts := by
  by_cases h4 : j < 4
  · rw [dhGens_lo h4]
    exact dConj_szj h4
  · have e : j = 4 := by omega
    subst e
    rw [dhGens_four, hArr_size]

theorem dhGens_size : dhGens.size = 5 := by
  unfold dhGens
  rw [Array.size_push, dConj_size]

theorem dhG_lt {j : Nat} (_hj : j < 5) {x : Nat} (hx : x < 245520) : dhG j x < 245520 :=
  lt_of_L lin_dhG hx

theorem dhInv_get {j : Nat} (hj : j < 5) {x : Nat} (hx : x < 245520) :
    (dhInv[j]!)[x]! = dhI j x := by
  have hs : (dhGens[j]!).size = 245520 := dhGens_size' hj
  unfold dhInv pinvs
  rw [getElem!_pos _ j (by simp [dhGens_size]; omega), Array.getElem_map,
    ← getElem!_pos dhGens j (by rw [dhGens_size]; exact hj), arr_ext hs fun y hy => dhGens_get hj hy]
  exact CFSG.KS.CB.pinvCand_get (fun y hy => dhG_lt hj hy) (fun y hy => rel_parts.1 j hj y hy) hx

theorem letters : LettersOK 245520 5 dhGens dhInv dhG dhI := fun _ hj _ hx =>
  ⟨dhGens_get hj hx, dhInv_get hj hx, dhG_lt hj hx, lt_of_L lin_dhI hx⟩

theorem pword_wDH {k : Nat} (hk : k < 8) {x : Nat} (hx : x < 245520) :
    (pword nPts dhGens dhInv (words8.getD k []))[x]! = wDH k x := by
  rw [(pword_get letters _ (let5 hk) x hx).1, wDH_eq hk]

theorem hGens_get {i : Nat} (hi : i < 4) {x : Nat} (hx : x < 245520) :
    (hGensArr[i]!)[x]! = hGK i x := by
  unfold hGensArr
  rw [pwords_get (by rw [show hWordsDH.size = 4 from rfl]; exact hi)]
  have e : hWordsDH[i]! = words8.getD i [] := by interval_cases i <;> rfl
  rw [e]
  exact pword_wDH (by omega) hx

theorem hGens_size : hGensArr.size = 4 := by
  unfold hGensArr
  rw [pwords_eq, Array.size_map]
  rfl

theorem mLK_lt {x : Nat} (hx : x < 245520) : mLK x < 245520 :=
  lt_of_L (lin_wDH (k := 4) (by norm_num)) hx

theorem mLift_get {x : Nat} (hx : x < 245520) : mLiftArr[x]! = mLK x :=
  pword_wDH (k := 4) (by norm_num) hx

theorem vArr_get {x : Nat} (hx : x < 245520) : vArr[x]! = vK x := by
  unfold vArr
  obtain ⟨c1, c2⟩ := c_get x hx
  obtain ⟨z1, z2⟩ := z_get _ c2
  rw [pcomp_get' hx, pcomp_get' hx, c1, z1, (ci_get _ z2).1]
  rfl

theorem vArr_size : vArr.size = nPts := by
  unfold vArr
  simp [Native.pcomp]

theorem vinv_get {x : Nat} (hx : x < 245520) : (pinvCand nPts vArr)[x]! = vK x := by
  rw [arr_ext vArr_size fun y hy => vArr_get hy]
  exact CFSG.KS.CB.pinvCand_get (fun y hy => lt_of_L lin_vK hy) (fun y hy => rel_parts.2.2.2.1 y hy) hx

theorem hvhv_get {x : Nat} (hx : x < 245520) : hvhvArr[x]! = hvhvK x := by
  unfold hvhvArr
  rw [pcomp_get' hx, pcomp_get' hx, pcomp_get' hx, vinv_get hx,
    (hArr_get _ (lt_of_L lin_vK hx)).1, vArr_get (lt_of_L lin_M2T (lt_of_L lin_vK hx)),
    hinv_get _ (lt_of_L lin_vK (lt_of_L lin_M2T (lt_of_L lin_vK hx)))]
  rfl

theorem qK_eq (k x : Nat) : qK k x = (QT^[k]) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change QT (qK k x) = _
    rw [ih, Function.iterate_succ_apply']

theorem lin_qK (k : Nat) : L (qK k) := by
  induction k with
  | zero => exact Lin.id
  | succ k ih => exact (Lin.comp lin_QT ih).congr fun _ _ => rfl

theorem qPow_get' (k : Nat) {x : Nat} (hx : x < 245520) : (qPowArr k)[x]! = qK k x := by
  rw [(qPow_get k hx).1, qK_eq]

theorem dSl_all : ∀ h < 144, ieAt dcK sp IDf PD LD QD 4 144 h = true :=
  ieSl_spec (q := 9) (L := 16) (by norm_num) fun s hs => dAll s hs

theorem dDist_parts : flD ≤ 154 ∧ distK (fpK IDf flD) 144 = true := by
  have h := d_dist
  unfold dDist at h
  rw [bAnd_iff] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, h.2⟩

@[expose] noncomputable def dRec : Enum :=
  ⟨Array.ofFn (n := 144) fun k => Array.ofFn (n := 245520) fun i => elt dcK PD LD k.val i.val,
    Array.ofFn (n := 144) fun i => PD i.val, Array.ofFn (n := 144) fun i => LD i.val⟩

theorem dEnum_sound : dEnum = dRec ∧ enumOK nPts dConj dRec = true :=
  ie_enumBFS orbit spans' (G := dcK) (fun j hj => lin_dcK hj) dConj_size
    (fun j hj x hx => (dConj_get hj hx).1) (by norm_num) dSl_all dDist_parts.2
    (fun a _ b _ h => fpK_congr dDist_parts.1 h) (by norm_num)

theorem eD_facts : ∀ k < 144, L (elt dcK PD LD k) ∧ ∀ t < 154, elt dcK PD LD k (sp t) = imgAt IDf k t :=
  ie_elt (fun j hj => lin_dcK hj) (by norm_num) dSl_all

theorem lin_eD {k : Nat} (hk : k < 144) : L (eD k) :=
  (eD_facts k hk).1.congr fun x _ => (eD_eq k x).symm

theorem asl_lt {i : Nat} (hi : i < 4) : asl i < 144 := by
  interval_cases i <;> decide +kernel

theorem asl_list : (List.range 144).filter (fun k => decide (tab ON8T.AS k ≠ 0)) = ASL := by
  decide +kernel

theorem conj_get {k : Nat} (hk : k < 144) {x : Nat} (hx : x < 245520) :
    (conjTab nPts hArr (pinvCand nPts hArr) (dRec.tabs[k]!))[x]! = M2T (eD k (hIK x)) := by
  have hi : hIK x < 245520 := lt_of_L lin_hIK hx
  have ht : (dRec.tabs[k]!) = Array.ofFn (n := 245520) fun i => elt dcK PD LD k i.val := by
    unfold dRec
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  unfold conjTab comp
  rw [getElem!_pos _ x (by simp; exact hx), Array.getElem_ofFn]
  simp only
  rw [hinv_get x hx, getElem!_pos _ (hIK x) (by simp; exact hi), Array.getElem_ofFn]
  simp only
  rw [ht, ofFn_get' hi, eD_eq, (hArr_get _ (lt_of_L (eD_facts k hk).1 hi)).1]

theorem aAt_spec {k : Nat} (hk : k < 144) :
    (dRec.tabs.any fun u => u == conjTab nPts hArr (pinvCand nPts hArr) (dRec.tabs[k]!)) =
      decide (tab ON8T.AS k ≠ 0) := by
  have h9 : k / 16 < 9 := by omega
  have ha := aAll (k / 16) h9
  unfold aSl at ha
  have h := allN_spec ha (k % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (k / 16) 16) (k % 16) = k := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  unfold aAt at h
  rw [strictB_app'] at h
  have hconj : L fun x => M2T (eD k (hIK x)) := Lin.comp lin_M2T (Lin.comp (lin_eD hk) lin_hIK)
  have hsz : dRec.tabs.size = 144 := by unfold dRec; exact Array.size_ofFn
  have hget : ∀ u < 144, dRec.tabs[u]! = Array.ofFn (n := 245520) fun i => elt dcK PD LD u i.val :=
    fun u hu => by
      unfold dRec
      rw [getElem!_pos _ u (by simpa using hu), Array.getElem_ofFn]
  have hcs : (conjTab nPts hArr (pinvCand nPts hArr) (dRec.tabs[k]!)).size = 245520 := by
    unfold conjTab comp
    rw [Array.size_ofFn]
  have cs := arr_ext (g := conjTab nPts hArr (pinvCand nPts hArr) (dRec.tabs[k]!)) (n := 245520)
    (F := fun i => M2T (eD k (hIK i))) hcs fun x hx => conj_get hk hx
  rw [cs]
  by_cases h0 : tab ON8T.AS k = 0
  · rw [h0] at h
    have hb0 : Nat.beq 0 0 = true := rfl
    rw [hb0] at h
    dsimp only at h
    rw [strictB_app'] at h
    rw [decide_eq_false (by simpa using h0), Bool.eq_false_iff]
    intro hany
    rw [Array.any_eq_true] at hany
    obtain ⟨u, hu, hu'⟩ := hany
    rw [hsz] at hu
    rw [← getElem!_pos dRec.tabs u (by rw [hsz]; exact hu), hget u hu, beq_iff_eq] at hu'
    have himg : ∀ t < 154, cjI k t = imgAt IDf u t := fun t ht => by
      rw [← (eD_facts u hu).2 t ht]
      have := congrArg (fun a : Array Nat => a[sp t]!) hu'
      rw [ofFn_get' (f := elt dcK PD LD u) (spans'.1 t ht),
        ofFn_get' (f := fun i => M2T (eD k (hIK i))) (spans'.1 t ht)] at this
      unfold cjI
      exact this.symm
    have hf : cjF k = fpK IDf flD u := fpF_congr fun t ht => himg t (by have := dDist_parts.1; omega)
    have := allN_spec h u hu
    rw [hf] at this
    simp at this
  · have hb : Nat.beq (tab ON8T.AS k) 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
    rw [hb] at h
    dsimp only at h
    rw [bAnd_iff] at h
    obtain ⟨hle, hall⟩ := h
    have hu : tab ON8T.AS k - 1 < 144 := by have := Nat.le_of_ble_eq_true hle; omega
    rw [decide_eq_true h0, Array.any_eq_true]
    refine ⟨tab ON8T.AS k - 1, by rw [hsz]; exact hu, ?_⟩
    rw [← getElem!_pos dRec.tabs _ (by rw [hsz]; exact hu), hget _ hu, beq_iff_eq]
    have hag := agree' (eD_facts _ hu).1 hconj (fun t ht => by
        rw [(eD_facts _ hu).2 t ht]
        exact (Nat.eq_of_beq_eq_true (allN_spec hall t ht)).symm)
    exact congrArg (fun f => Array.ofFn (n := 245520) f) (funext fun i => hag i.val i.isLt)

@[expose] noncomputable def TD (k : Nat) : Array Nat :=
  Array.ofFn (n := 245520) fun i => elt dcK PD LD k i.val

theorem dRec_get {k : Nat} (hk : k < 144) : dRec.tabs[k]! = TD k := by
  unfold dRec TD
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem ASL_len : ASL.length = 4 := by decide +kernel

theorem aTabs_eq : aTabs = (ASL.map TD).toArray := by
  unfold aTabs
  rw [dEnum_sound.1]
  have e : dRec.tabs = Array.ofFn (n := 144) fun k => TD k.val := rfl
  conv_lhs => rw [e]
  rw [filter_ofFn (m := 144) (f := TD)]
  congr 2
  rw [← asl_list]
  apply List.filter_congr
  intro k hk
  have hk' : k < 144 := List.mem_range.1 hk
  rw [← dRec_get hk', ← aAt_spec hk', ← e]

theorem aTabs_size : aTabs.size = 4 := by
  rw [aTabs_eq, List.size_toArray, List.length_map, ASL_len]

theorem aTabs_get {i : Nat} (hi : i < 4) : aTabs[i]! = TD (asl i) := by
  rw [aTabs_eq, getElem!_pos _ i (by simp [ASL_len]; exact hi), List.getElem_toArray,
    List.getElem_map]
  unfold asl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [ASL_len]; exact hi)]
  rfl

theorem TD_get {k : Nat} {x : Nat} (hx : x < 245520) : (TD k)[x]! = eD k x := by
  unfold TD
  rw [ofFn_get' hx, eD_eq]

theorem aT_get {i : Nat} (hi : i < 4) {x : Nat} (hx : x < 245520) : (aTabs[i]!)[x]! = eD (asl i) x := by
  rw [aTabs_get hi, TD_get hx]

theorem eD_lt {k : Nat} (hk : k < 144) {x : Nat} (hx : x < 245520) : eD k x < 245520 :=
  lt_of_L (lin_eD hk) hx

theorem hSl_all : ∀ h < 144, ieAt hGK sp IHf PH LH QH 4 144 h = true :=
  ieSl_spec (q := 9) (L := 16) (by norm_num) fun s hs => hAll s hs

theorem hDist_parts : flH ≤ 154 ∧ distK (fpK IHf flH) 144 = true := by
  have h := h_dist
  unfold hDist at h
  rw [bAnd_iff] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, h.2⟩

theorem lin_hGK {i : Nat} (hi : i < 4) : L (hGK i) := lin_wDH (k := i) (by omega)

@[expose] noncomputable def hRec : Enum :=
  ⟨Array.ofFn (n := 144) fun k => Array.ofFn (n := 245520) fun i => elt hGK PH LH k.val i.val,
    Array.ofFn (n := 144) fun i => PH i.val, Array.ofFn (n := 144) fun i => LH i.val⟩

theorem hEnum_sound : hEnum = hRec ∧ enumOK nPts hGensArr hRec = true :=
  ie_enumBFS orbit spans' (G := hGK) (fun j hj => lin_hGK hj) hGens_size
    (fun j hj x hx => hGens_get hj hx) (by norm_num) hSl_all hDist_parts.2
    (fun a _ b _ h => fpK_congr hDist_parts.1 h) (by norm_num)

theorem eH_facts : ∀ k < 144, L (elt hGK PH LH k) ∧ ∀ t < 154, elt hGK PH LH k (sp t) = imgAt IHf k t :=
  ie_elt (fun j hj => lin_hGK hj) (by norm_num) hSl_all

theorem lin_eH {k : Nat} (hk : k < 144) : L (eH k) :=
  (eH_facts k hk).1.congr fun x _ => (eH_eq k x).symm

theorem hRec_get {k : Nat} (hk : k < 144) :
    hRec.tabs[k]! = Array.ofFn (n := 245520) fun i => eH k i.val := by
  unfold hRec
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  congr 1
  funext i
  rw [eH_eq]

theorem ofFn_eq {F G : Nat → Nat} (h : ∀ x < 245520, F x = G x) :
    (Array.ofFn (n := 245520) fun i => F i.val) = Array.ofFn (n := 245520) fun i => G i.val :=
  congrArg (fun f => Array.ofFn (n := 245520) f) (funext fun i => h i.val i.isLt)

theorem comp_get {a b : Array Nat} {F G : Nat → Nat} (ha : ∀ x < 245520, a[x]! = F x)
    (hb : ∀ x < 245520, b[x]! = G x) (hG : ∀ x < 245520, G x < 245520) :
    comp nPts a b = Array.ofFn (n := 245520) fun i => F (G i.val) := by
  unfold comp
  congr 1
  funext i
  rw [hb _ i.isLt, ha _ (hG _ i.isLt)]

theorem comp_comm_of {a b : Array Nat} {F G : Nat → Nat} (ha : ∀ x < 245520, a[x]! = F x)
    (hb : ∀ x < 245520, b[x]! = G x) (hF : ∀ x < 245520, F x < 245520)
    (hG : ∀ x < 245520, G x < 245520) (h : ∀ x < 245520, F (G x) = G (F x)) :
    comp nPts a b = comp nPts b a := by
  apply Array.ext
  · unfold comp
    rw [Array.size_ofFn, Array.size_ofFn]
  · intro i h1 h2
    have hi : i < 245520 := by
      unfold comp at h1
      rw [Array.size_ofFn] at h1
      exact h1
    simp only [comp, Array.getElem_ofFn]
    rw [hb i hi, ha _ (hG i hi), ha i hi, hb _ (hF i hi)]
    exact h i hi

theorem pid_eq : pid nPts = Array.ofFn (n := 245520) fun i => i.val := rfl

theorem bpt_lt' {b : Nat} (hb : b < 3) : bpt b < 245520 := by
  interval_cases b <;> decide

theorem rep7 (c : Nat) (hc : c < 144) : ∀ (k : Nat) {p : Nat}, p < 245520 →
    Nat.repeat (fun x => hArr[(hRec.tabs[c]!)[x]!]!) k p =
      Nat.rec (motive := fun _ => Nat) p (fun _ acc => M2T (eH c acc)) k ∧
    Nat.rec (motive := fun _ => Nat) p (fun _ acc => M2T (eH c acc)) k < 245520
  | 0, p, hp => ⟨rfl, hp⟩
  | k + 1, p, hp => by
    obtain ⟨e, hlt⟩ := rep7 c hc k hp
    have hl2 : eH c (Nat.rec (motive := fun _ => Nat) p (fun _ acc => M2T (eH c acc)) k) < 245520 :=
      lt_of_L (lin_eH hc) hlt
    change (fun x => hArr[(hRec.tabs[c]!)[x]!]!) (Nat.repeat _ k p) = _ ∧ _
    beta_reduce
    rw [e, hRec_get hc, ofFn_get' hlt, (hArr_get _ hl2).1]
    exact ⟨rfl, lt_of_L lin_M2T hl2⟩

theorem tag_ok {c : Nat} (hc : c < 144) :
    (hRec.tabs[c]! == pid nPts || hRec.tabs[c]! == hvhvArr || order7Moves (hRec.tabs[c]!)) = true := by
  have h9 : c / 16 < 9 := by omega
  have ht := tAll (c / 16) h9
  unfold tSl at ht
  have h := allN_spec ht (c % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (c / 16) 16) (c % 16) = c := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  unfold tAt at h
  rw [strictB_app'] at h
  generalize hgd : tab ON8T.HT c = g at h
  rw [Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
  have hR := hRec_get hc
  by_cases g0 : g = 0
  · subst g0
    have hb0 : Nat.beq 0 0 = true := rfl
    rw [hb0] at h
    dsimp only at h
    left
    left
    rw [hR]
    have hag := agree' (lin_eH hc) Lin.id fun t ht => by
      rw [eH_eq, (eH_facts c hc).2 t ht]
      exact Nat.eq_of_beq_eq_true (allN_spec h t ht)
    exact congrArg (fun f => Array.ofFn (n := 245520) f) (funext fun i => hag i.val i.isLt)
  · have hb0 : Nat.beq g 0 = false := Bool.eq_false_iff.2 fun e => g0 (Nat.eq_of_beq_eq_true e)
    rw [hb0] at h
    dsimp only at h
    by_cases g1 : g = 1
    · subst g1
      have hb1 : Nat.beq 1 1 = true := rfl
      rw [hb1] at h
      dsimp only at h
      left
      right
      have hsz : hvhvArr.size = 245520 := by
        unfold hvhvArr Native.pcomp
        rw [Array.size_ofFn]
      rw [hR, arr_ext (n := 245520) (F := hvhvK) hsz fun x hx => hvhv_get hx]
      have hl : L hvhvK := by
        unfold hvhvK
        exact Lin.comp lin_hIK (Lin.comp lin_vK (Lin.comp lin_M2T lin_vK))
      have hag := agree' (lin_eH hc) hl fun t ht => by
        rw [eH_eq, (eH_facts c hc).2 t ht]
        exact Nat.eq_of_beq_eq_true (allN_spec h t ht)
      exact congrArg (fun f => Array.ofFn (n := 245520) f) (funext fun i => hag i.val i.isLt)
    · have hb1 : Nat.beq g 1 = false := Bool.eq_false_iff.2 fun e => g1 (Nat.eq_of_beq_eq_true e)
      rw [hb1] at h
      dsimp only at h
      rw [bAnd_iff] at h
      obtain ⟨hb, hne⟩ := h
      have hb' : g - 2 < 3 := Nat.blt_eq.mp hb
      right
      unfold order7Moves
      rw [Array.any_eq_true]
      refine ⟨g - 2, by simp; omega, ?_⟩
      have ep : (#[0, 227759, 100817] : Array Nat)[g - 2]'(by simp; omega) = bpt (g - 2) := by
        generalize hbd : g - 2 = b at hb' ⊢
        interval_cases b <;> rfl
      rw [ep, (rep7 c hc 7 (bpt_lt' hb')).1]
      have hne' : it7 c (bpt (g - 2)) ≠ bpt (g - 2) := by
        intro e'
        have hb2 : Nat.beq (it7 c (bpt (g - 2))) (bpt (g - 2)) = true := by
          rw [e']
          exact Nat.beq_refl _
        change (!(Nat.beq (it7 c (bpt (g - 2))) (bpt (g - 2)))) = true at hne
        rw [hb2] at hne
        exact absurd hne (by decide)
      exact bne_iff_ne.2 hne'

theorem part1 : (dConj.all (fun g => g.size == nPts) = true ∧ enumOK nPts dConj dEnum = true ∧
      dEnum.tabs.size = 144 ∧ aTabs.size = 4 ∧
      hGensArr.all (fun g => g.size == nPts) = true ∧ enumOK nPts hGensArr hEnum = true ∧
      hEnum.tabs.size = 144 ∧
      hGensArr.all (fun g => aTabs.all fun a => comp nPts g a == comp nPts a g) = true ∧
      hEnum.tabs.all (fun c => c == pid nPts || c == hvhvArr || order7Moves c) = true) := by
  obtain ⟨dE, dOK⟩ := dEnum_sound
  obtain ⟨hE, hOK⟩ := hEnum_sound
  refine ⟨?_, by rw [dE]; exact dOK, by rw [dE]; exact Array.size_ofFn, aTabs_size, ?_,
    by rw [hE]; exact hOK, by rw [hE]; exact Array.size_ofFn, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    rw [dConj_size] at hi
    rw [← getElem!_pos dConj i (by rw [dConj_size]; exact hi), dConj_szj hi]
    exact beq_self_eq_true _
  · rw [Array.all_eq_true]
    intro i hi
    have e : hGensArr[i] = pword nPts dhGens dhInv hWordsDH[i]! := by
      rw [← getElem!_pos hGensArr i hi]
      unfold hGensArr
      exact pwords_get (by rw [hGens_size] at hi; exact hi)
    rw [e, pword_size]
    exact beq_self_eq_true _
  · rw [Array.all_eq_true]
    intro i hi
    rw [hGens_size] at hi
    rw [Array.all_eq_true]
    intro a ha
    rw [aTabs_size] at ha
    rw [← getElem!_pos hGensArr i (by rw [hGens_size]; exact hi),
      ← getElem!_pos aTabs a (by rw [aTabs_size]; exact ha), beq_iff_eq]
    have hag := agree (F := fun x => hGK i (eD (asl a) x)) (G := fun x => eD (asl a) (hGK i x))
      (Lin.comp (lin_hGK hi) (lin_eD (asl_lt ha))) (Lin.comp (lin_eD (asl_lt ha)) (lin_hGK hi))
      (rel_parts.2.2.2.2.2.2 i hi a ha)
    exact comp_comm_of (fun x hx => hGens_get hi hx) (fun x hx => aT_get ha hx)
      (fun x hx => lt_of_L (lin_hGK hi) hx) (fun x hx => eD_lt (asl_lt ha) hx) hag
  · rw [hE, Array.all_eq_true]
    intro c hc
    have hc' : c < 144 := by
      have e144 : hRec.tabs.size = 144 := Array.size_ofFn
      rw [e144] at hc
      exact hc
    rw [← getElem!_pos hRec.tabs c hc]
    exact tag_ok hc'

theorem neAt_spec {F G : Nat → Nat} {i : Nat} (h : neAt F G i = true) :
    wit i < 245520 ∧ F (wit i) ≠ G (wit i) := by
  unfold neAt at h
  rw [strictB_app', bAnd_iff] at h
  exact ⟨Nat.blt_eq.mp h.1, fun e => by simp [e] at h⟩

theorem nePair_spec {m : Nat} {F G : Nat → Nat → Nat} {i : Nat} (h : nePair m F G i = true) :
    wit i < m ∧ wit (i + 1) < 245520 ∧ F (wit i) (wit (i + 1)) ≠ G (wit i) (wit (i + 1)) := by
  unfold nePair at h
  rw [strictB_app', strictB_app'] at h
  simp only [bAnd_iff] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2.1, fun e => by simp [e] at h⟩

theorem wit_parts : neAt vK (fun x => x) 0 = true ∧ neAt vK ZT 1 = true ∧
    neAt (fun x => vK (M2T x)) (fun x => M2T (vK x)) 2 = true ∧
    nePair 3 (fun j x => QT (mG j x)) (fun j x => mG j (QT x)) 3 = true ∧
    nePair 3 (fun j x => qK 3 (mG j x)) (fun j x => mG j (qK 3 x)) 5 = true ∧
    nePair 4 (fun j x => QT (dcK j x)) (fun j x => dcK j (QT x)) 7 = true ∧
    nePair 4 (fun j x => qK 3 (dcK j x)) (fun j x => dcK j (qK 3 x)) 9 = true ∧
    nePair 4 (fun j x => QT (eD (asl j) x)) (fun j x => eD (asl j) (QT x)) 11 = true ∧
    nePair 4 (fun j x => qK 3 (eD (asl j) x)) (fun j x => eD (asl j) (qK 3 x)) 13 = true ∧
    ∀ k < 4, nePair 4 (fun j x => mLK (qK k (eD (asl j) x)))
      (fun j x => eD (asl j) (mLK (qK k x))) (Nat.add 15 (Nat.mul 2 k)) = true := by
  have h := wit_ok
  unfold witOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun k hk => allN_spec h10 k hk⟩

theorem all13 (f : Nat → Bool) (h1 : f 1 = true) (h3 : f 3 = true) :
    (#[1, 3] : Array Nat).all f = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 2 := by simpa using hi
  interval_cases i
  · exact h1
  · exact h3

theorem notAll_of {m j : Nat} {p : Nat → Bool} (hj : j < m) (h : p j = false) :
    (!(allBelowN m p)) = true := by
  rw [Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro ha
  rw [CertificateChecks.KernelSpor.ON3.allBelowN_iff.1 ha j hj] at h
  exact absurd h (by decide)

theorem mArr_get {j : Nat} (hj : j < 3) {x : Nat} (hx : x < 245520) :
    ((wordArrs Data.MWords)[j]!)[x]! = mG j x := (m_get hj x hx).1

theorem lin_mG' {j : Nat} (hj : j < 3) {x : Nat} (hx : x < 245520) : mG j x < 245520 :=
  (m_get hj x hx).2

theorem qk_noncomm_M (k : Nat) (i : Nat)
    (h : nePair 3 (fun j x => qK k (mG j x)) (fun j x => mG j (qK k x)) i = true) :
    (!(allBelowN 3 fun j => peq nPts (pcomp nPts (qPowArr k) (wordArrs Data.MWords)[j]!)
      (pcomp nPts (wordArrs Data.MWords)[j]! (qPowArr k)))) = true := by
  obtain ⟨hj, hx, hne⟩ := nePair_spec h
  refine notAll_of hj (peq_false_of' hx ?_)
  rw [pcomp_get' hx, pcomp_get' hx, mArr_get hj hx, qPow_get' k (lin_mG' hj hx), qPow_get' k hx,
    mArr_get hj (lt_of_L (lin_qK k) hx)]
  exact hne

theorem qk_noncomm_D (k : Nat) (i : Nat)
    (h : nePair 4 (fun j x => qK k (dcK j x)) (fun j x => dcK j (qK k x)) i = true) :
    (!(allBelowN 4 fun j => peq nPts (pcomp nPts (qPowArr k) dConj[j]!)
      (pcomp nPts dConj[j]! (qPowArr k)))) = true := by
  obtain ⟨hj, hx, hne⟩ := nePair_spec h
  refine notAll_of hj (peq_false_of' hx ?_)
  rw [pcomp_get' hx, pcomp_get' hx, (dConj_get hj hx).1, qPow_get' k (dConj_get hj hx).2,
    qPow_get' k hx, (dConj_get hj (lt_of_L (lin_qK k) hx)).1]
  exact hne

theorem notAllA {p : Array Nat → Bool} {j : Nat} (hj : j < 4) (h : p (aTabs[j]!) = false) :
    (!(aTabs.all p)) = true := by
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro ha
  rw [Array.all_eq_true] at ha
  have := ha j (by rw [aTabs_size]; exact hj)
  rw [← getElem!_pos aTabs j (by rw [aTabs_size]; exact hj), h] at this
  exact absurd this (by decide)

theorem qk_noncomm_A (k : Nat) (i : Nat)
    (h : nePair 4 (fun j x => qK k (eD (asl j) x)) (fun j x => eD (asl j) (qK k x)) i = true) :
    (!(aTabs.all fun a => peq nPts (pcomp nPts (qPowArr k) a) (pcomp nPts a (qPowArr k)))) = true := by
  obtain ⟨hj, hx, hne⟩ := nePair_spec h
  refine notAllA hj (peq_false_of' hx ?_)
  rw [pcomp_get' hx, pcomp_get' hx, aT_get hj hx, qPow_get' k (eD_lt (asl_lt hj) hx),
    qPow_get' k hx, aT_get hj (lt_of_L (lin_qK k) hx)]
  exact hne

theorem repeat_zero' {α : Type} (f : α → α) (a : α) : Nat.repeat f 0 a = a := rfl

theorem repeat_succ' {α : Type} (f : α → α) (k : Nat) (a : α) :
    Nat.repeat f (k + 1) a = f (Nat.repeat f k a) := rfl

theorem rep_h (k : Nat) {x : Nat} (hx : x < 245520) :
    (Nat.repeat (pcomp nPts hArr) k (pid nPts))[x]! =
      Nat.rec (motive := fun _ => Nat) x (fun _ acc => M2T acc) k ∧
    Nat.rec (motive := fun _ => Nat) x (fun _ acc => M2T acc) k < 245520 := by
  induction k with
  | zero =>
    rw [repeat_zero']
    exact ⟨pid_get' (n := nPts) hx, hx⟩
  | succ k ih =>
    obtain ⟨e, hlt⟩ := ih
    rw [repeat_succ', pcomp_get' (n := nPts) hx, e, (hArr_get _ hlt).1]
    exact ⟨rfl, (hArr_get _ hlt).2⟩

theorem part2 : (allBelowN 5 (fun j => pisInv nPts dhGens[j]! dhInv[j]!) = true ∧
      allBelowN 3 (fun j => plettersOK 5 mWordsDH[j]! &&
        peq nPts (pword nPts dhGens dhInv mWordsDH[j]!) (wordArrs Data.MWords)[j]!) = true ∧
      hWordsDH.all (plettersOK 5) = true ∧
      peq nPts (Nat.repeat (pcomp nPts hArr) 7 (pid nPts)) (pid nPts) = true ∧
      memIn MStrong Data.MChain.base vArr = true ∧
      peq nPts (pcomp nPts vArr vArr) (pid nPts) = true ∧
      peq nPts vArr (pid nPts) = false ∧ peq nPts vArr zArr = false ∧
      allBelowN 4 (fun j => peq nPts (pcomp nPts vArr dConj[j]!) (pcomp nPts dConj[j]! vArr)) =
        true ∧
      peq nPts (pcomp nPts vArr hArr) (pcomp nPts hArr vArr) = false ∧
      peq nPts zArr (qPowArr 2) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(allBelowN 3 fun j =>
        peq nPts (pcomp nPts (qPowArr k) (wordArrs Data.MWords)[j]!)
          (pcomp nPts (wordArrs Data.MWords)[j]! (qPowArr k)))) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(allBelowN 4 fun j =>
        peq nPts (pcomp nPts (qPowArr k) dConj[j]!) (pcomp nPts dConj[j]! (qPowArr k)))) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(aTabs.all fun a =>
        peq nPts (pcomp nPts (qPowArr k) a) (pcomp nPts a (qPowArr k)))) = true) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, -⟩ := rel_parts
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, -⟩ := wit_parts
  obtain ⟨n1, n1'⟩ := neAt_spec w1
  obtain ⟨n2, n2'⟩ := neAt_spec w2
  obtain ⟨n3, n3'⟩ := neAt_spec w3
  refine ⟨CertificateChecks.KernelSpor.ON3.allBelowN_iff.2 fun j hj => ?_, CertificateChecks.KernelSpor.ON3.allBelowN_iff.2 fun j hj => ?_,
    by rw [← Array.all_toList]; decide,
    peq_of' fun x hx => ?_, memM' (G := vK) (fun k hk => vArr_get (CertificateChecks.KernelSpor.ON3.bB_lt hk))
      (fun k hk => lt_of_L lin_vK (CertificateChecks.KernelSpor.ON3.bB_lt hk)) v_sift,
    peq_of' fun x hx => ?_, peq_false_of' n1 ?_, peq_false_of' n2 ?_,
    CertificateChecks.KernelSpor.ON3.allBelowN_iff.2 fun j hj => peq_of' fun x hx => ?_, peq_false_of' n3 ?_, peq_of' fun x hx => ?_,
    all13 _ (qk_noncomm_M 1 3 w4) (qk_noncomm_M 3 5 w5),
    all13 _ (qk_noncomm_D 1 7 w6) (qk_noncomm_D 3 9 w7),
    all13 _ (qk_noncomm_A 1 11 w8) (qk_noncomm_A 3 13 w9)⟩
  · have e : dhInv[j]! = pinvCand nPts dhGens[j]! := by
      unfold dhInv pinvs
      rw [getElem!_pos _ j (by simp [dhGens_size]; omega), Array.getElem_map,
        ← getElem!_pos dhGens j (by rw [dhGens_size]; exact hj)]
    rw [e]
    exact pisInv_of (dhGens_size' hj) (fun x hx => dhGens_get hj hx)
      fun x hx => ⟨dhG_lt hj hx, r1 j hj x hx⟩
  · rw [Bool.and_eq_true]
    refine ⟨by interval_cases j <;> decide, peq_of' fun x hx => ?_⟩
    have e : mWordsDH[j]! = words8.getD (5 + j) [] := by interval_cases j <;> rfl
    rw [e, pword_wDH (by omega) hx, mArr_get hj hx]
    exact r2 j hj x hx
  · rw [(rep_h 7 hx).1, pid_get' hx]
    exact r3 x hx
  · rw [pcomp_get' hx, vArr_get hx, vArr_get (lt_of_L lin_vK hx), pid_get' hx]
    exact r4 x hx
  · rw [vArr_get n1, pid_get' n1]
    exact n1'
  · rw [vArr_get n2, (z_get _ n2).1]
    exact n2'
  · rw [pcomp_get' hx, pcomp_get' hx, (dConj_get hj hx).1, vArr_get (dConj_get hj hx).2,
      vArr_get hx, (dConj_get hj (lt_of_L lin_vK hx)).1]
    exact r5 j hj x hx
  · rw [pcomp_get' n3, pcomp_get' n3, (hArr_get _ n3).1, vArr_get (hArr_get _ n3).2, vArr_get n3,
      (hArr_get _ (lt_of_L lin_vK n3)).1]
    exact n3'
  · rw [(z_get x hx).1, qPow_get' 2 hx]
    exact r6 x hx

theorem blk_parts : ASL.length = 4 ∧ AB.length = 5 ∧
    (∀ i < 5, blkK (abF i) (abK i) = true ∧ canonK 120 7 (mask 7) 840 (abP i) = true ∧
      ∀ b < 120, abK i b = pg 7 (mask 7) (abP i) b) ∧
    ∀ a < 4, pcomp 120 7 (mask 7) (abP 4) (abP a) = pcomp 120 7 (mask 7) (abP a) (abP 4) := by
  have h := blk_ok
  unfold blkOK at h
  simp only [bAnd_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun i hi => ?_, fun a ha => Nat.eq_of_beq_eq_true (allN_spec h4 a ha)⟩
  have := allN_spec h3 i hi
  simp only [bAnd_iff] at this
  exact ⟨this.1, this.2.1, fun b hb => Nat.eq_of_beq_eq_true (allN_spec this.2.2 b hb)⟩

theorem abF_lt {i : Nat} (hi : i < 4) (x : Nat) : abF i x = eD (asl i) x := by
  unfold abF
  rw [nIf_lt hi]

theorem bTab_parts {g : Array Nat} {i : Nat} (hi : i < 5) (hg : ∀ y < 245520, g[y]! = abF i y) :
    blockImgOK g Data.quotientBlocks (bTab g) = true ∧ bTab g = unpack 120 7 (abP i) := by
  obtain ⟨-, -, hb, -⟩ := blk_parts
  obtain ⟨b1, -, b3⟩ := hb i hi
  obtain ⟨t1, t2⟩ := blockTab_of hg b1
  refine ⟨t1, ?_⟩
  rw [t2]
  unfold unpack
  congr 1
  funext b
  exact b3 b.val b.isLt

theorem aBlk {a : Nat} (ha : a < 4) :
    blockImgOK aTabs[a]! Data.quotientBlocks (bTab aTabs[a]!) = true ∧
      bTab aTabs[a]! = unpack 120 7 (abP a) :=
  bTab_parts (by omega) fun y hy => by rw [aT_get ha hy, abF_lt ha]

theorem mBlk : blockImgOK mLiftArr Data.quotientBlocks (bTab mLiftArr) = true ∧
    bTab mLiftArr = unpack 120 7 (abP 4) :=
  bTab_parts (by norm_num) fun y hy => mLift_get hy

theorem canon120 {i : Nat} (hi : i < 5) : canonK 120 7 (mask 7) (120 * 7) (abP i) = true :=
  (blk_parts.2.2.1 i hi).2.1

theorem gensA : GensOK 120 7 4 abP (aTabs.map bTab) := by
  refine ⟨by rw [Array.size_map, aTabs_size], fun j hj => ⟨?_, canon120 (i := j) (by omega)⟩⟩
  rw [getElem!_pos _ j (by simp [aTabs_size]; exact hj), Array.getElem_map,
    ← getElem!_pos aTabs j (by rw [aTabs_size]; exact hj)]
  exact (aBlk hj).2

theorem qA_pt {i : Nat} (hi : i < ON5M.cnt) :
    ((aTabs.map bTab).all fun g => comp 120 (unpack 120 7 (ON5M.T i)) g ==
      comp 120 g (unpack 120 7 (ON5M.T i))) = qA i := by
  rw [all_comm gensA (penumPt_canon (CertificateChecks.KernelSpor.ON5K.m_pt hi))]
  unfold qA
  rw [strictB_app']

theorem m120_count : (m120Enum.tabs.filter fun x => aTabs.all fun a =>
    comp 120 x (bTab a) == comp 120 (bTab a) x).size = 144 := by
  have me : m120Enum = penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL :=
    (penumK_left_sound (cap := 50000) CertificateChecks.KernelSpor.ON5K.szOK120
      (gensOK_of CertificateChecks.KernelSpor.ON5K.m_gens) CertificateChecks.KernelSpor.ON5K.m_hd
      fun _ hi => CertificateChecks.KernelSpor.ON5K.m_pt hi).1
  rw [me]
  simp only [penumRec]
  rw [filter_ofFn (m := ON5M.cnt) (f := fun i => unpack 120 7 (ON5M.T i)), List.size_toArray,
    List.length_map]
  have hcnt : ON5M.cnt = 2016 * 20 := rfl
  have e : ((List.range ON5M.cnt).filter fun i => aTabs.all fun a =>
      comp 120 (unpack 120 7 (ON5M.T i)) (bTab a) == comp 120 (bTab a) (unpack 120 7 (ON5M.T i))) =
      (List.range ON5M.cnt).filter qA := by
    apply List.filter_congr
    intro i hi
    have hi' : i < ON5M.cnt := List.mem_range.1 hi
    rw [← qA_pt hi', Array.all_map]
    rfl
  rw [e, hcnt, blocks_eq qA 2016 mselIn 20 fun s hs => by
    have h := selFrom_spec qA 2016 _ _ (mAll s hs)
    have e2 : Nat.mul s 2016 = 2016 * s := Nat.mul_comm s 2016
    rw [e2] at h
    exact h]
  have hd : ((List.range 20).flatMap mselIn).length = 144 := by decide +kernel
  exact hd

theorem mq_noncomm {k : Nat} (hk : k < 4) :
    (!(aTabs.all fun a => peq nPts (pcomp nPts (pcomp nPts mLiftArr (qPowArr k)) a)
      (pcomp nPts a (pcomp nPts mLiftArr (qPowArr k))))) = true := by
  obtain ⟨hj, hx, hne⟩ := nePair_spec (wit_parts.2.2.2.2.2.2.2.2.2 k hk)
  refine notAllA hj (peq_false_of' hx ?_)
  have h1 : eD (asl (wit (Nat.add 15 (Nat.mul 2 k)))) (wit (Nat.add 15 (Nat.mul 2 k) + 1)) < 245520 :=
    eD_lt (asl_lt hj) hx
  rw [pcomp_get' hx, pcomp_get' hx, aT_get hj hx, pcomp_get' h1, qPow_get' k h1,
    mLift_get (lt_of_L (lin_qK k) h1), pcomp_get' hx, qPow_get' k hx,
    mLift_get (lt_of_L (lin_qK k) hx), aT_get hj (mLK_lt (lt_of_L (lin_qK k) hx))]
  exact hne

theorem part3 : (aTabs.all (fun a => blockImgOK a Data.quotientBlocks (bTab a)) = true ∧
      (m120Enum.tabs.filter fun x => aTabs.all fun a =>
        comp 120 x (bTab a) == comp 120 (bTab a) x).size = 144 ∧
      plettersOK 5 liftWordDH = true ∧
      blockImgOK mLiftArr Data.quotientBlocks (bTab mLiftArr) = true ∧
      aTabs.all (fun a => comp 120 (bTab mLiftArr) (bTab a) == comp 120 (bTab a) (bTab mLiftArr)) =
        true ∧
      allBelowN 4 (fun k => !(aTabs.all fun a =>
        peq nPts (pcomp nPts (pcomp nPts mLiftArr (qPowArr k)) a)
          (pcomp nPts a (pcomp nPts mLiftArr (qPowArr k))))) = true) := by
  refine ⟨?_, m120_count, by decide, mBlk.1, ?_, CertificateChecks.KernelSpor.ON3.allBelowN_iff.2 fun k hk => mq_noncomm hk⟩
  · rw [Array.all_eq_true]
    intro a ha
    rw [aTabs_size] at ha
    rw [← getElem!_pos aTabs a (by rw [aTabs_size]; exact ha)]
    exact (aBlk ha).1
  · rw [Array.all_eq_true]
    intro a ha
    rw [aTabs_size] at ha
    rw [← getElem!_pos aTabs a (by rw [aTabs_size]; exact ha), (aBlk ha).2, mBlk.2,
      comp_unpackG (canon120 (i := 4) (by norm_num)) (canon120 (i := a) (by omega)),
      comp_unpackG (canon120 (i := a) (by omega)) (canon120 (i := 4) (by norm_num)), blk_parts.2.2.2 a ha]
    exact beq_self_eq_true _

theorem part4 : pisInv nPts vArr (pinvCand nPts vArr) = true :=
  pisInv_of vArr_size (fun _ hx => vArr_get hx) fun x hx => ⟨lt_of_L lin_vK hx, rel_parts.2.2.2.1 x hx⟩

open Certificates in
open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.PSL3Four.Native in
theorem facts2214 : (dConj.all (fun g => g.size == nPts) = true ∧ enumOK nPts dConj dEnum = true ∧
      dEnum.tabs.size = 144 ∧ aTabs.size = 4 ∧
      hGensArr.all (fun g => g.size == nPts) = true ∧ enumOK nPts hGensArr hEnum = true ∧
      hEnum.tabs.size = 144 ∧
      hGensArr.all (fun g => aTabs.all fun a => comp nPts g a == comp nPts a g) = true ∧
      hEnum.tabs.all (fun c => c == pid nPts || c == hvhvArr || order7Moves c) = true
    )
    ∧ (allBelowN 5 (fun j => pisInv nPts dhGens[j]! dhInv[j]!) = true ∧
      allBelowN 3 (fun j => plettersOK 5 mWordsDH[j]! &&
        peq nPts (pword nPts dhGens dhInv mWordsDH[j]!) (wordArrs Data.MWords)[j]!) = true ∧
      hWordsDH.all (plettersOK 5) = true ∧
      peq nPts (Nat.repeat (pcomp nPts hArr) 7 (pid nPts)) (pid nPts) = true ∧
      memIn MStrong Data.MChain.base vArr = true ∧
      peq nPts (pcomp nPts vArr vArr) (pid nPts) = true ∧
      peq nPts vArr (pid nPts) = false ∧ peq nPts vArr zArr = false ∧
      allBelowN 4 (fun j => peq nPts (pcomp nPts vArr dConj[j]!) (pcomp nPts dConj[j]! vArr)) =
        true ∧
      peq nPts (pcomp nPts vArr hArr) (pcomp nPts hArr vArr) = false ∧
      peq nPts zArr (qPowArr 2) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(allBelowN 3 fun j =>
        peq nPts (pcomp nPts (qPowArr k) (wordArrs Data.MWords)[j]!)
          (pcomp nPts (wordArrs Data.MWords)[j]! (qPowArr k)))) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(allBelowN 4 fun j =>
        peq nPts (pcomp nPts (qPowArr k) dConj[j]!) (pcomp nPts dConj[j]! (qPowArr k)))) = true ∧
      (#[1, 3] : Array Nat).all (fun k => !(aTabs.all fun a =>
        peq nPts (pcomp nPts (qPowArr k) a) (pcomp nPts a (qPowArr k)))) = true
    )
    ∧ (aTabs.all (fun a => blockImgOK a Data.quotientBlocks (bTab a)) = true ∧
      (m120Enum.tabs.filter fun x => aTabs.all fun a =>
        comp 120 x (bTab a) == comp 120 (bTab a) x).size = 144 ∧
      plettersOK 5 liftWordDH = true ∧
      blockImgOK mLiftArr Data.quotientBlocks (bTab mLiftArr) = true ∧
      aTabs.all (fun a => comp 120 (bTab mLiftArr) (bTab a) == comp 120 (bTab a) (bTab mLiftArr)) =
        true ∧
      allBelowN 4 (fun k => !(aTabs.all fun a =>
        peq nPts (pcomp nPts (pcomp nPts mLiftArr (qPowArr k)) a)
          (pcomp nPts a (pcomp nPts mLiftArr (qPowArr k))))) = true
    )
    ∧ (pisInv nPts vArr (pinvCand nPts vArr) = true) := ⟨part1, part2, part3, part4⟩

end CertificateChecks.KernelSpor.ON8

end
