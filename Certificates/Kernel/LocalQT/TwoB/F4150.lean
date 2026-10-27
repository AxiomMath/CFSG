module

public import Certificates.Kernel.LocalQT.TwoB.C4150
public import Certificates.Kernel.LocalQT.TwoB.C4150C
public import Certificates.Kernel.LocalQT.TwoB.C4150N
public import Certificates.Kernel.LocalQT.TwoB.C4150H0
public import Certificates.Kernel.LocalQT.TwoB.C4150H1
public import Certificates.Kernel.LocalQT.SV.C4126TB
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHSTwoBInputs
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.TB.E CFSG.KD.LQT.TB.ckE 90
#kqb_all CFSG.KD.LQT.TB.HF CFSG.KD.LQT.TB.ckHF 45
#kqb_all CFSG.KD.LQT.TB.C CFSG.KD.LQT.TB.ckC 180
#kqb_all CFSG.KD.LQT.TB.N CFSG.KD.LQT.TB.ckN 360
#kqb_all CFSG.KD.LQT.TB.M CFSG.KD.LQT.TB.ckM 8

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native

theorem commAll_of {n w cnt K : Nat} {T PL C CI POS : Nat → Nat} {cs : List Table}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true) (hcs : TabsOK n w K C cs.toArray)
    (hci : ∀ j < K, invEqK n w (mask w) (n * w) (C j) (CI j) = true ∧
      canonK n w (mask w) (n * w) (CI j) = true)
    (hf : ∀ c < K * K, findPtK cnt T (commQK n w (mask w) K C CI) POS c = true) :
    cs.all (fun c => cs.all fun c' => memT n (hRec n w cnt T PL).1
      (compT n (compT n (compT n c c') (invT n c)) (invT n c'))) = true := by
  have get : ∀ j (hj : j < cs.length), j < K →
      cs[j] = tabT (unpack n w (C j)) ∧ canonK n w (mask w) (n * w) (C j) = true := by
    intro j hj hjK
    obtain ⟨h1, h2⟩ := hcs.2 j hjK
    refine ⟨?_, h2⟩
    rw [← h1, getElem!_pos _ j (by simpa using hj)]
    simp
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hc
  rw [List.all_eq_true]
  intro c' hc'
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hc'
  have ha' : a < K := by rw [← hcs.1]; simpa using ha
  have hb' : b < K := by rw [← hcs.1]; simpa using hb
  obtain ⟨ea, ca⟩ := get a ha ha'
  obtain ⟨eb, cb⟩ := get b hb hb'
  have hc : a * K + b < K * K := by
    have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt ha')
    rw [Nat.succ_mul] at this
    omega
  obtain ⟨hq, he⟩ := findPt_spec (hf _ hc)
  unfold commQK at he
  obtain ⟨e1, e2⟩ := div_mod_pair (i := a) hb'
  rw [show Nat.div (a * K + b) K = a from e1, show Nat.mod (a * K + b) K = b from e2] at he
  have hia := invT_unpack (lt_of_canonK (hci a ha').2) (hci a ha').1
  have hib := invT_unpack (lt_of_canonK (hci b hb').2) (hci b hb').1
  rw [ea, eb, hia, hib, compT_unpack ca cb, compT_unpack (canonK_pcomp ca cb) (hci a ha').2,
    compT_unpack (canonK_pcomp (canonK_pcomp ca cb) (hci a ha').2) (hci b hb').2, ← he]
  exact memT_of hq (tblEq_self (hT _ hq))

theorem commOK_of {n w k cnt cap K : Nat} {G GI T PL POS SRT SRI HS HSI C CI CM : Nat → Nat}
    {gs cs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (hcs : TabsOK n w K C cs.toArray)
    (hci : ∀ j < K, invEqK n w (mask w) (n * w) (C j) (CI j) = true ∧
      canonK n w (mask w) (n * w) (CI j) = true)
    (hf : ∀ c < K * K, findPtK cnt T (commQK n w (mask w) K C CI) CM c = true) :
    CFSG.QuasithinUnique.Id2519.SporHS.commOK n cap gs cs = true := by
  obtain ⟨e, _, _⟩ := mulH_sound hn hG hg hh hp hs
  have hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true :=
    fun i hi => penumPt_canon (hp i hi)
  unfold CFSG.QuasithinUnique.Id2519.SporHS.commOK
  simp only []
  rw [e]
  exact commAll_of hT hcs hci hf

end CFSG.KS.MulH

namespace CFSG.KD.LQT.TB

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native CFSG.KD.LQT.C4126
open CFSG.QuasithinUnique.Id2519.SporHS

theorem base : szOK 3850 12 = true ∧ canonK 3850 12 (mask 12) (3850 * 12) idK = true ∧
    CFSG.KS.Prim.idK 3850 12 (mask 12) = true ∧
    allN 4 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (cC j)) = true ∧
    allN 4 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (cCI j)) = true ∧
    allN 2 (fun j => Nat.beq (Y.G j) idK) = true ∧
    Nat.beq (Y.GI 0) (wfoldK 3850 12 (mask 12) cL [4, 2, 1, 4] idK) = true ∧
    Nat.beq (Y.GI 1) (wfoldK 3850 12 (mask 12) cL [3, 3] idK) = true ∧
    allN 2 (fun j => invEqK 3850 12 (mask 12) (3850 * 12) (Y.GI j) (YI j)) = true ∧
    allN 2 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (YI j)) = true ∧
    penumHdK idK Y.cnt 400 Y.T Y.PL = true ∧ Nat.beq Y.cnt 360 = true := by
  simpa only [bAnd_iff] using base_ok

theorem hn : szOK 3850 12 = true := base.1

theorem hidc : canonK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) = true := base.2.1

theorem hid : idT 3850 = tabT (unpack 3850 12 (pidn 3850 12)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem cnt_eq : Y.cnt = 360 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.2.2.2.2

theorem cent_tab {k : Nat} (hk : k < 43) : hsCentTbl k = tabT (unpack 3850 12 (HC.F k)) := by
  rw [← hsCentTbl_eq hk, tabT_natArr]

theorem c_inv : ∀ j < 4, invEqK 3850 12 (mask 12) (3850 * 12) (cC j) (cCI j) = true ∧
    canonK 3850 12 (mask 12) (3850 * 12) (cCI j) = true :=
  fun j hj => ⟨allN_spec hc_perms (13 + j) (by omega), allN_spec base.2.2.2.2.1 j hj⟩

theorem c_get {j : Nat} (hj : j < 4) :
    twoBGens.getD j (idT 3850) = tabT (unpack 3850 12 (cC j)) := by
  interval_cases j <;> simp only [twoBGens, List.getD_cons_succ, List.getD_cons_zero]
  · exact cent_tab (k := 13) (by norm_num)
  · exact cent_tab (k := 14) (by norm_num)
  · exact cent_tab (k := 15) (by norm_num)
  · exact cent_tab (k := 16) (by norm_num)

theorem c_tabs : TabsOK 3850 12 4 cC twoBGens.toArray := by
  refine ⟨rfl, fun j hj => ⟨?_, allN_spec base.2.2.2.1 j hj⟩⟩
  rw [← c_get hj, List.getElem!_toArray]
  interval_cases j <;> simp [twoBGens]

theorem cL_ok {l : Nat} (h1 : 1 ≤ l) (h4 : l ≤ 4) :
    twoBGens.getD (l - 1) (idT 3850) = tabT (unpack 3850 12 (cL l)) ∧
      canonK 3850 12 (mask 12) (3850 * 12) (cL l) = true := by
  have hc := allN_spec base.2.2.2.1 (l - 1) (by omega)
  have hg := c_get (j := l - 1) (by omega)
  interval_cases l
  · exact ⟨hg, hc⟩
  · exact ⟨hg, hc⟩
  · exact ⟨hg, hc⟩
  · exact ⟨hg, hc⟩

theorem word {wd : List Nat} (hw : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 4) :
    wordTbl 3850 twoBGens wd =
        tabT (unpack 3850 12 (wfoldK 3850 12 (mask 12) cL wd (pidn 3850 12))) ∧
      canonK 3850 12 (mask 12) (3850 * 12) (wfoldK 3850 12 (mask 12) cL wd (pidn 3850 12)) =
        true :=
  wordTbl_unpack hid hidc fun l hl => cL_ok (hw l hl).1 (hw l hl).2

theorem y_tabs : TabsOK 3850 12 2 Y.GI twoBY.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · obtain ⟨h1, h2⟩ := word (wd := [4, 2, 1, 4]) (by decide)
    have e : twoBY.toArray[0]! = wordTbl 3850 twoBGens [4, 2, 1, 4] := by simp [twoBY]
    rw [Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.1, e]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := word (wd := [3, 3]) (by decide)
    have e : twoBY.toArray[1]! = wordTbl 3850 twoBGens [3, 3] := by simp [twoBY]
    rw [Nat.eq_of_beq_eq_true base.2.2.2.2.2.2.2.1, e]
    exact ⟨h1, h2⟩

theorem y_inv : ∀ j < 2, invEqK 3850 12 (mask 12) (3850 * 12) (Y.GI j) (YI j) = true ∧
    canonK 3850 12 (mask 12) (3850 * 12) (YI j) = true :=
  fun j hj => ⟨allN_spec base.2.2.2.2.2.2.2.2.1 j hj, allN_spec base.2.2.2.2.2.2.2.2.2.1 j hj⟩

theorem y_ids : ∀ j < 2, Y.G j = pidn 3850 12 :=
  fun j hj => Nat.eq_of_beq_eq_true (allN_spec base.2.2.2.2.2.1 j hj)

theorem hd : penumHdK (pidn 3850 12) Y.cnt 400 Y.T Y.PL = true := base.2.2.2.2.2.2.2.2.2.2.1

theorem chunks {L N : Nat} {P : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, Nat.mul s L ≤ i → i < Nat.mul s L + L → P i) : ∀ i < N * L, P i := by
  intro i hi
  exact h (i / L) (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)) i
    (Nat.div_mul_le_self i L) (Nat.lt_div_mul_add hL)

theorem pe : ∀ i < Y.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) true Y.G Y.GI 2 Y.cnt Y.T Y.PL
    Y.POS Y.SRT Y.SRI i = true := by
  intro i hi
  rw [cnt_eq] at hi
  refine chunks (N := 90) (L := 4) (P := fun i => penumPtK 3850 12 (mask 12) (3850 * 12) true
    Y.G Y.GI 2 Y.cnt Y.T Y.PL Y.POS Y.SRT Y.SRI i = true) (by norm_num)
    (fun s hs j h1 h2 => ?_) i hi
  change j < s * 4 + 4 at h2
  exact penumSl_spec (E.all s hs) j h1 h2 (by rw [cnt_eq]; omega)

theorem hs : ∀ i < Y.cnt, hsortPtK 3850 12 (mask 12) Y.cnt Y.T Y.HS Y.HSI i = true := by
  intro i hi
  rw [← hsortPtKF_eq 3850 12 Y.cnt Y.T Y.HS Y.HSI i]
  rw [cnt_eq] at hi
  refine chunks (N := 45) (L := 8)
    (P := fun i => hsortPtKF 3850 12 (mask 12) Y.cnt Y.T Y.HS Y.HSI i = true) (by norm_num)
    (fun s hs j h1 h2 => ?_) i hi
  change j < s * 8 + 8 at h2
  exact slK_spec (HF.all s hs) j h1 h2 (by rw [cnt_eq]; omega)

theorem cl : ∀ c < Y.cnt * (2 + 2), findPtK Y.cnt Y.T
    (prodQK 3850 12 (mask 12) (2 + 2) Y.T (bothK 2 Y.GI YI)) YCl c = true := by
  intro i hi
  simp only [cnt_eq] at hi
  refine chunks (N := 180) (L := 8) (P := fun i => findPtK Y.cnt Y.T
    (prodQK 3850 12 (mask 12) (2 + 2) Y.T (bothK 2 Y.GI YI)) YCl i = true) (by norm_num)
    (fun s hs j h1 h2 => ?_) i hi
  change j < s * 8 + 8 at h2
  exact slK_spec (C.all s hs) j h1 h2 (by change j < Y.cnt * 4; rw [cnt_eq]; omega)

theorem nm : ∀ c < Y.cnt * 4, findPtK Y.cnt Y.T (conjQK 3850 12 (mask 12) 4 Y.T cC cCI) YNm c =
    true := by
  intro i hi
  rw [cnt_eq] at hi
  refine chunks (N := 360) (L := 4) (P := fun i => findPtK Y.cnt Y.T
    (conjQK 3850 12 (mask 12) 4 Y.T cC cCI) YNm i = true) (by norm_num)
    (fun s hs j h1 h2 => ?_) i hi
  change j < s * 4 + 4 at h2
  exact slK_spec (N.all s hs) j h1 h2 (by change j < Y.cnt * 4; rw [cnt_eq]; omega)

theorem cm : ∀ c < 4 * 4, findPtK Y.cnt Y.T (commQK 3850 12 (mask 12) 4 cC cCI) YCm c = true := by
  intro i hi
  refine chunks (N := 8) (L := 2) (P := fun i => findPtK Y.cnt Y.T
    (commQK 3850 12 (mask 12) 4 cC cCI) YCm i = true) (by norm_num)
    (fun s hs j h1 h2 => ?_) i hi
  change j < s * 2 + 2 at h2
  exact slK_spec (M.all s hs) j h1 h2 (by omega)

theorem twoB_check : twoBCheck = true := by
  have hgens : twoBGens.all (fun g => permOK 3850 g && invOK 3850 g (invT 3850 g)) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list c_tabs hg
    rw [invT_unpack (lt_of_canonK (c_inv j hj).2) (c_inv j hj).1, Bool.and_eq_true]
    exact ⟨permOK_unpack hc (c_inv j hj).1, invOK_unpack hc (c_inv j hj).2 (c_inv j hj).1⟩
  have hy : twoBY.all (fun g => permOK 3850 g) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list y_tabs hg
    exact permOK_unpack hc (y_inv j hj).1
  have henum : enumOK 3850 400 360 twoBY = true :=
    enumOK_of hn y_ids y_tabs y_inv hd pe hs cl cnt_eq
  have hnorm : normOK 3850 400 twoBY twoBGens = true :=
    normOK_of hn y_ids y_tabs hd pe hs c_tabs c_inv nm
  have hcomm : commOK 3850 400 twoBY twoBGens = true :=
    commOK_of hn y_ids y_tabs hd pe hs c_tabs c_inv cm
  unfold twoBCheck
  rw [hgens, hy, henum, hnorm, hcomm]
  rfl

end CFSG.KD.LQT.TB

end
