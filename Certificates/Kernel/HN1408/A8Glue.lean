module

public import Certificates.Kernel.HN1408.A8Chk
public import Certificates.Kernel.HN1408.A8ChkS
public import Certificates.Kernel.HN1408.Spec
public import Certificates.Kernel.HN1408.M11Lem
public import Certificates.Kernel.HN1408.TableIGlue
public import CFSG.Certificates.Kernel.Spor.MulHFSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem commEq_of {U V UI VI A : Nat} (hU : Cn U) (hV : Cn V) (hUI : Cn UI) (hVI : Cn VI)
    (hA : Cn A) (iu : invEqK 1408 11 (mask 11) (1408 * 11) U UI = true)
    (iv : invEqK 1408 11 (mask 11) (1408 * 11) V VI = true)
    (h : Nat.beq (pc (pc (pc U V) UI) VI) A = true) :
    commutatorEqOK (tabT (unpack 1408 11 U)) (tabT (unpack 1408 11 V)) (tabT (unpack 1408 11 A)) =
      true := by
  unfold commutatorEqOK
  rw [invT_unpack (by norm_num) iu, invT_unpack (by norm_num) iv, invOK_unpack hU hUI iu,
    invOK_unpack hV hVI iv, compT_unpack hU hV, compT_unpack (canonK_pcomp hU hV) hUI,
    compT_unpack (canonK_pcomp (canonK_pcomp hU hV) hUI) hVI,
    tblEq_eq (canonK_pcomp (canonK_pcomp (canonK_pcomp hU hV) hUI) hVI) hA]
  simpa [pc] using h

theorem orbRowOK_of {cap korder X CI cntO cntS : Nat} {kg : List (List Nat)} {wy : List Nat}
    {r : OrbRow}
    {OG OGI OT OPL OPOS OSRT OSRI OHS OHSI SG SGI ST SPL SPOS SSRT SSRI SHS SHSI : Nat → Nat}
    (hkg : ∀ w ∈ kg, lettersOK w = true) (hwy : lettersOK wy = true)
    (hcj : lettersOK r.conj = true) (hst : ∀ w ∈ r.stabWords kg, lettersOK w = true)
    (hCI : Cn CI) (hci : invEqK 1408 11 (mask 11) (1408 * 11) (WK r.conj) CI = true)
    (hX : pc (pc (WK r.conj) (WK wy)) CI = X)
    (hOG : ∀ j < kg.length, OG j = WK (kg.getD j []) ∧ Cn (OGI j) ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (OG j) (OGI j) = true)
    (hOh : penumHdK X cntO cap OT OPL = true)
    (hOp : ∀ i < cntO, penumPtK 1408 11 (mask 11) (1408 * 11) true OG OGI kg.length cntO OT OPL
      OPOS OSRT OSRI i = true)
    (hOs : ∀ i < cntO, hsortPtK 1408 11 (mask 11) cntO OT OHS OHSI i = true)
    (hSG : ∀ j < (r.stabWords kg).length, SG j = idK ∧
      SGI j = WK ((r.stabWords kg).getD j []) ∧ commP (SGI j) X = true)
    (hSh : penumHdK idK cntS cap ST SPL = true)
    (hSp : ∀ i < cntS, penumPtK 1408 11 (mask 11) (1408 * 11) true SG SGI (r.stabWords kg).length
      cntS ST SPL SPOS SSRT SSRI i = true)
    (hSs : ∀ i < cntS, hsortPtK 1408 11 (mask 11) cntS ST SHS SHSI i = true)
    (hm : cntO = r.m) (hn' : cntS = r.n) (hk : r.m * r.n = korder) :
    orbRowOK cap kg wy korder r = true := by
  have hcX : Cn X := by
    rw [← hX]
    exact cn_pc (cn_pc (cn_WK hcj) (cn_WK hwy)) hCI
  have hc : r.repTab wy = tabT (unpack 1408 11 X) := by
    unfold OrbRow.repTab conjTab
    rw [(tabW_eq hcj).1, (tabW_eq hwy).1, invT_unpack (by norm_num) hci,
      conjT_unpack (cn_WK hcj) hCI (cn_WK hwy), ← hX]
    rfl
  have cO : ∀ j < kg.length, Cn (OG j) := fun j hj => by
    rw [(hOG j hj).1]
    exact cn_WK (lettersOK_getD hkg j)
  have tO : TabsOK 1408 11 kg.length OG (p0Tabs kg) := tabsW_tabs hkg fun j hj => (hOG j hj).1
  have tOI : TabsOK 1408 11 kg.length OGI (p0Invs kg) :=
    TabsOK_inv tO fun j hj => ⟨(hOG j hj).2.2, (hOG j hj).2.1⟩
  obtain ⟨eO, tOk, dO⟩ := conjH_sound (X := X) (x := tabT (unpack 1408 11 X)) hn tO tOI rfl hOh
    hOp hOs
  have tS : TabsOK 1408 11 (r.stabWords kg).length SGI (p0Tabs (r.stabWords kg)) :=
    tabsW_tabs hst fun j hj => (hSG j hj).2.1
  obtain ⟨eS, tSk, dS⟩ := mulH_sound hn (fun j hj => (hSG j hj).1) tS hSh hSp hSs
  have aW : kg.all wordOK = true := by
    rw [List.all_eq_true]
    exact fun w hw => wordOK_of (hkg w hw)
  have aI : kg.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) = true :=
    allW (f := fun t => invOK 1408 t (invT 1408 t)) rfl (fun j hj => (hOG j hj).1) hkg
      fun j hj => by
        change invOK 1408 _ (invT 1408 _) = true
        rw [invT_unpack (by norm_num) (hOG j hj).2.2]
        exact invOK_unpack (cO j hj) (hOG j hj).2.1 (hOG j hj).2.2
  have aC : invOK 1408 (tabW r.conj) (invT 1408 (tabW r.conj)) = true := by
    rw [(tabW_eq hcj).1, invT_unpack (by norm_num) hci]
    exact invOK_unpack (cn_WK hcj) hCI hci
  have aS : commWordsOK (r.stabWords kg) (tabT (unpack 1408 11 X)) = true := by
    unfold commWordsOK
    exact allW (f := fun t => commTT 1408 t (tabT (unpack 1408 11 X))) rfl
      (fun j hj => (hSG j hj).2.1) hst fun j hj => by
        have cS : Cn (SGI j) := by
          rw [(hSG j hj).2.1]
          exact cn_WK (lettersOK_getD hst j)
        change commTT 1408 _ _ = true
        rw [commTT_eq cS hcX]
        exact (hSG j hj).2.2
  dsimp only [orbRowOK]
  rw [hc, eO, eS, gensOK_true, wordOK_of hwy, wordOK_of hcj, aW, aI, aC, tOk, dO, aS, tSk, dS,
    hRec_size, hRec_size, hm, hn', hk]
  simp

theorem a8_hlk : ∀ w ∈ classb.centGens, lettersOK w = true := by decide

theorem a8_hlr : ∀ w ∈ classb.centGens.map List.reverse, lettersOK w = true := by decide

theorem a8_hst : ∀ w ∈ a8Row.stabWords classb.centGens, lettersOK w = true := by
  intro w hw
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
  exact lettersOK_specWord a8_hlk s

theorem a8_WK_stab (j : Nat) :
    WK ((a8Row.stabWords classb.centGens).getD j []) =
      specK (classb.centGens.map WK) (a8Row.stab.getD j []) := by
  unfold OrbRow.stabWords
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a8Row.stab[j]? with
  | none => rfl
  | some s => exact WK_specWord a8_hlk s

theorem a8_lU : lettersOK a8W0 = true := lettersOK_specWord a8_hlk a8SU

theorem a8_eU : WK a8W0 = a8U := WK_specWord a8_hlk a8SU

theorem a8_hdO : (∀ j < 2, A8O.G j = WK (classb.centGens.getD j []) ∧ Cn (A8O.GI j) ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (A8O.G j) (A8O.GI j) = true) ∧ A8O.cnt = 105 ∧
    A8O.R = a8U ∧ penumHdK A8O.R A8O.cnt 100000 A8O.T A8O.PL = true := by
  have h := a8kHdO
  unfold a8HdO at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h5, h6⟩ := h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h5, h6⟩
  have h7 := allN_spec h1 j hj
  simp only [bAnd_iff] at h7
  obtain ⟨a, b, c⟩ := h7
  exact ⟨Nat.eq_of_beq_eq_true a, b, c⟩

theorem a8_hdS : (∀ j < 5, A8S.G j = idK ∧
      A8S.GI j = specK (classb.centGens.map WK) (a8Row.stab.getD j []) ∧
      commP (A8S.GI j) A8O.R = true) ∧ A8S.cnt = 768 ∧
    penumHdK idK A8S.cnt 100000 A8S.T A8S.PL = true := by
  have h := a8kHdS
  unfold a8HdS at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h3, h4⟩ := h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h3, h4⟩
  have h7 := allN_spec h1 j hj
  simp only [bAnd_iff] at h7
  obtain ⟨a, b, c⟩ := h7
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c⟩

theorem a8_inv : invEqK 1408 11 (mask 11) (1408 * 11) (specK (classb.centGens.map WK) a8SX)
      (specK ((classb.centGens.map List.reverse).map WK) a8SX.reverse) = true ∧
    invEqK 1408 11 (mask 11) (1408 * 11) (specK (classb.centGens.map WK) a8SY)
      (specK ((classb.centGens.map List.reverse).map WK) a8SY.reverse) = true ∧
    invEqK 1408 11 (mask 11) (1408 * 11) (WK a8WZ) (WK a8WZ.reverse) = true ∧
    invEqK 1408 11 (mask 11) (1408 * 11) idK idK = true := by
  have h := a8kInv
  simp only [bAnd_iff] at h
  exact h

theorem a8_orbRow : orbRowOK a8Cap classb.centGens a8W0 80640 a8Row = true := by
  obtain ⟨hG, hc, hR, hh⟩ := a8_hdO
  obtain ⟨sG, sc, sh⟩ := a8_hdS
  have hRO := a8kRecO
  unfold a8RecO at hRO
  simp only [bAnd_iff] at hRO
  obtain ⟨pO, hsO⟩ := hRO
  have hK : classb.centGens.length = 2 := rfl
  have hL : (a8Row.stabWords classb.centGens).length = 5 := rfl
  have eC : WK a8Row.conj = idK := rfl
  have hX : pc (pc (WK a8Row.conj) (WK a8W0)) idK = A8O.R := by
    rw [eC, pc_idL (cn_WK a8_lU), pc_idR (cn_WK a8_lU), a8_eU, hR]
  have hG' : ∀ j < classb.centGens.length, A8O.G j = WK (classb.centGens.getD j []) ∧
      Cn (A8O.GI j) ∧ invEqK 1408 11 (mask 11) (1408 * 11) (A8O.G j) (A8O.GI j) = true := by
    rw [hK]
    exact hG
  have hOp : ∀ i < A8O.cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true A8O.G A8O.GI
      classb.centGens.length A8O.cnt A8O.T A8O.PL A8O.POS A8O.SRT A8O.SRI i = true := by
    rw [hK]
    exact fun i hi => penumSl_spec pO i (Nat.zero_le _) (by omega) hi
  have hOs : ∀ i < A8O.cnt, hsortPtK 1408 11 (mask 11) A8O.cnt A8O.T A8O.HS A8O.HSI i = true :=
    fun i hi => by
      rw [← hsortPtKF_eq 1408 11 A8O.cnt A8O.T A8O.HS A8O.HSI i]
      exact slK_spec hsO i (Nat.zero_le _) (by omega) hi
  have hSG : ∀ j < (a8Row.stabWords classb.centGens).length, A8S.G j = idK ∧
      A8S.GI j = WK ((a8Row.stabWords classb.centGens).getD j []) ∧
      commP (A8S.GI j) A8O.R = true := by
    rw [hL]
    intro j hj
    rw [a8_WK_stab]
    exact sG j hj
  have hSp' : ∀ i < A8S.cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true A8S.G A8S.GI 5 A8S.cnt
      A8S.T A8S.PL A8S.POS A8S.SRT A8S.SRI i = true :=
    peAll (L := 256) (K := 3) (by rw [sc]) fun s hs => by
      match s, hs with
      | 0, _ => exact a8kPeS0
      | 1, _ => exact a8kPeS1
      | 2, _ => exact a8kPeS2
  have hSp : ∀ i < A8S.cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true A8S.G A8S.GI
      (a8Row.stabWords classb.centGens).length A8S.cnt A8S.T A8S.PL A8S.POS A8S.SRT A8S.SRI i =
      true := by
    rw [hL]
    exact hSp'
  have hSs : ∀ i < A8S.cnt, hsortPtK 1408 11 (mask 11) A8S.cnt A8S.T A8S.HS A8S.HSI i = true :=
    fun i hi => by
      rw [← hsortPtKF_eq 1408 11 A8S.cnt A8S.T A8S.HS A8S.HSI i]
      exact slK_spec a8kHsS i (Nat.zero_le _) (by omega) hi
  have hh' : penumHdK A8O.R A8O.cnt a8Cap A8O.T A8O.PL = true := hh
  have sh' : penumHdK idK A8S.cnt a8Cap A8S.T A8S.PL = true := sh
  have hm : A8O.cnt = a8Row.m := hc
  have hn' : A8S.cnt = a8Row.n := sc
  have hk : a8Row.m * a8Row.n = 80640 := rfl
  have hcj : lettersOK a8Row.conj = true := rfl
  exact orbRowOK_of a8_hlk a8_lU hcj a8_hst cId a8_inv.2.2.2 hX hG' hh' hOp hOs hSG sh' hSp hSs
    hm hn' hk

theorem a8LabelOK_true : a8LabelOK = true := by
  have lX : lettersOK a8WX = true := lettersOK_specWord a8_hlk a8SX
  have lY : lettersOK a8WY = true := lettersOK_specWord a8_hlk a8SY
  have eX : WK a8WX = specK (classb.centGens.map WK) a8SX := WK_specWord a8_hlk a8SX
  have eY : WK a8WY = specK (classb.centGens.map WK) a8SY := WK_specWord a8_hlk a8SY
  have lZ : lettersOK wordZ = true := by decide
  have lZR : lettersOK a8WZ.reverse = true := by decide
  have cU : Cn a8U := cn_specK a8_hlk a8SU
  obtain ⟨i1, i2, i3, -⟩ := a8_inv
  unfold a8LabelOK
  rw [gensOK_true, wordOK_of lX, wordOK_of lY, wordOK_of a8_lU, (tabW_eq lX).1, (tabW_eq lY).1,
    (tabW_eq a8_lU).1, (tabW_eq lZ).1, eX, eY, a8_eU,
    commEq_of (A := a8U) (cn_specK a8_hlk a8SX) (cn_specK a8_hlk a8SY)
      (cn_specK a8_hlr a8SX.reverse) (cn_specK a8_hlr a8SY.reverse) cU i1 i2 a8kComm,
    conjEqOK_of (Z := a8U) (by decide) (cn_WK lZR) i3 (cn_WK lZ) cU a8kConj, a8_orbRow]
  rfl

end CFSG.KD.HN1408

end
