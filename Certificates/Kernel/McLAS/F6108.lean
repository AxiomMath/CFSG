module

public import Certificates.Kernel.McLAS.Glue
public import Certificates.Kernel.McLAS.RecKChk0
public import Certificates.Kernel.McLAS.RecKChk1
public import Certificates.Kernel.McLAS.RecKChk2
public import Certificates.Kernel.McLAS.RecKChk3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.McLAS

theorem k6108 : bAnd(allN 3 (fun j => bAnd(Nat.beq (RK.G j) McLAS.idK,
      bAnd(Nat.beq (RK.GI j) (TT.F j), bAnd(Nat.beq (PO.G j) (TT.F j), Nat.beq (PO.GI j) (TTI j))))),
    bAnd(Nat.beq PO.R (PT.F 0), bAnd(penumHdK McLAS.idK RK.cnt 924000 RK.T RK.PL,
    bAnd(penumHdK (PT.F 0) PO.cnt 200 PO.T PO.PL, bAnd(Nat.beq PO.cnt 180,
    bAnd(Nat.ble RK.cnt 29200,
    bAnd(recSlK true PO.G PO.GI 3 PO.cnt PO.T PO.PL PO.POS PO.SRT PO.SRI PO.HS PO.HSI 0 200,
    bAnd(Nat.beq (fixK (TT.F 0)) 5, bAnd(sK (PT.F 0),
    bAnd(Nat.beq (pcomp 275 9 (mask 9) (PT.F 0) (TT.F 0)) (pcomp 275 9 (mask 9) (TT.F 0) (PT.F 0)),
      pairSelK (TT.F 0) (PT.F 0))))))))))) = true := by
  quickRfl

theorem f6108 :
    (∀ j < 3, RK.G j = McLAS.idK ∧ RK.GI j = TT.F j ∧ PO.G j = TT.F j ∧ PO.GI j = TTI j) ∧
    PO.R = PT.F 0 ∧ penumHdK McLAS.idK RK.cnt 924000 RK.T RK.PL = true ∧
    penumHdK (PT.F 0) PO.cnt 200 PO.T PO.PL = true ∧ PO.cnt = 180 ∧ RK.cnt ≤ 29200 ∧
    recSlK true PO.G PO.GI 3 PO.cnt PO.T PO.PL PO.POS PO.SRT PO.SRI PO.HS PO.HSI 0 200 = true ∧
    fixK (TT.F 0) = 5 ∧ sK (PT.F 0) = true ∧
    pcomp 275 9 (mask 9) (PT.F 0) (TT.F 0) = pcomp 275 9 (mask 9) (TT.F 0) (PT.F 0) ∧
    pairSelK (TT.F 0) (PT.F 0) = true := by
  have h := k6108
  simp only [bAnd_iff, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨fun j hj => ?_, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hj' := allN_spec h1 j hj
  simp only [bAnd_iff, Nat.beq_eq] at hj'
  exact hj'

theorem rk_le : RK.cnt ≤ 200 * 146 := f6108.2.2.2.2.2.1

theorem cK_all : ∀ s < 146, cK s = true :=
  join4 (a := 37) (b := 37) (c := 36) (d := 36) CK0.all CK1.all CK2.all CK3.all

theorem rk_spec : (∀ i < RK.cnt, penumPtK 275 9 (mask 9) (275 * 9) true RK.G RK.GI 3 RK.cnt RK.T
      RK.PL RK.POS RK.SRT RK.SRI i = true) ∧
    (∀ i < RK.cnt, hsortPtK 275 9 (mask 9) RK.cnt RK.T RK.HS RK.HSI i = true) :=
  rec_spec (cnt := RK.cnt) (NS := 146) rk_le fun s hs => ((bAnd_iff _ _).1 (cK_all s hs)).1

theorem rk_sel : ∀ i < RK.cnt, selK i = true := by
  intro i hi
  have hle := rk_le
  have hs := (bAnd_iff _ _).1 (cK_all (i / 200) (by omega))
  have h1 : (i / 200) * 200 ≤ i := Nat.div_mul_le_self i 200
  have h2 : i < (i / 200) * 200 + 200 := by omega
  exact slK_spec hs.2 i h1 h2 hi

theorem po_spec : (∀ i < PO.cnt, penumPtK 275 9 (mask 9) (275 * 9) true PO.G PO.GI 3 PO.cnt PO.T
      PO.PL PO.POS PO.SRT PO.SRI i = true) ∧
    (∀ i < PO.cnt, hsortPtK 275 9 (mask 9) PO.cnt PO.T PO.HS PO.HSI i = true) := by
  have hc : PO.cnt ≤ 200 * 1 := by rw [f6108.2.2.2.2.1]; omega
  refine rec_spec (cnt := PO.cnt) (NS := 1) hc fun s hs => ?_
  have hs0 : s = 0 := by omega
  subst hs0
  exact f6108.2.2.2.2.2.2.1

theorem cg_eq : threeRow₁.centGens.toArray =
    #[tabT (unpack 275 9 (TT.F 0)), tabT (unpack 275 9 (TT.F 1)), tabT (unpack 275 9 (TT.F 2))] := by
  have h0 := tabTT (k := 0) (by norm_num)
  have h1 := tabTT (k := 1) (by norm_num)
  have h2 := tabTT (k := 2) (by norm_num)
  change #[threeTbl 0, threeTbl 1, threeTbl 2] = _
  rw [h0, h1, h2]

theorem tabs_cg (G : Nat → Nat) (hG : ∀ j < 3, G j = TT.F j) :
    TabsOK 275 9 3 G threeRow₁.centGens.toArray := by
  rw [cg_eq]
  refine ⟨rfl, fun j hj => ?_⟩
  rw [hG j hj]
  refine ⟨?_, TTc (by omega)⟩
  interval_cases j <;> rfl

theorem tabs_cgi : TabsOK 275 9 3 PO.GI (threeRow₁.centGens.toArray.map (invT 275)) :=
  TabsOK_inv (tabs_cg PO.G fun j hj => (f6108.1 j hj).2.2.1) fun j hj => by
    rw [(f6108.1 j hj).2.2.1, (f6108.1 j hj).2.2.2]
    exact ⟨TTinv (by omega), TTIc (by omega)⟩

theorem rk_canon {i : Nat} (hi : i < RK.cnt) : Cn (RK.T i) := penumPt_canon (rk_spec.1 i hi)

theorem cg_ok {j : Nat} (hj : j < 11) :
    (permOK 275 (tabT (unpack 275 9 (TT.F j))) &&
      invOK 275 (tabT (unpack 275 9 (TT.F j))) (invT 275 (tabT (unpack 275 9 (TT.F j))))) =
      true := by
  rw [invT_unpack (by norm_num) (TTinv hj), Bool.and_eq_true]
  exact ⟨permOK_unpack (TTc hj) (TTinv hj), invOK_unpack (TTc hj) (TTIc hj) (TTinv hj)⟩

theorem rk_sel_mem {i : Nat} (hi : i < RK.cnt) :
    (!pairSel (threeTbl 0) (tabT (unpack 275 9 (RK.T i))) ||
      memT 275 (hRec 275 9 PO.cnt PO.T PO.PL).1 (tabT (unpack 275 9 (RK.T i)))) = true := by
  have hA := TTc (k := 0) (by norm_num)
  have hc := rk_canon hi
  rw [tabTT (by norm_num), pairSel_eq hA hc]
  have hs := rk_sel i hi
  unfold selK at hs
  rw [PEnum.strictB_app', (f6108.1 0 (by norm_num)).2.1] at hs
  cases e : pairSelK (TT.F 0) (RK.T i) with
  | false => rfl
  | true =>
    rw [e] at hs
    unfold atK at hs
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hs
    have hq : r32 KinPO i < PO.cnt := Nat.le_of_ble_eq_true h1
    have hT : PO.T (r32 KinPO i) = RK.T i := Nat.eq_of_beq_eq_true h2
    have hm := memT_of (n := 275) (w := 9) (T := PO.T) (PL := PO.PL) hq (x := tabT (unpack 275 9 (RK.T i)))
      (by rw [hT]; exact tblEq_self hc)
    rw [hm]
    rfl

theorem pairCheck_true : pairCheck = true := by
  obtain ⟨hgs, hR, hhK, hhP, hPc, -, -, hfix, hsift, hcomm, hsel⟩ := f6108
  have hM := mulH_sound (k := 3) hn (fun j hj => (hgs j hj).1)
    (tabs_cg RK.GI fun j hj => (hgs j hj).2.1) hhK rk_spec.1 rk_spec.2
  have hC := conjH_sound (k := 3) (X := PT.F 0) hn (tabs_cg PO.G fun j hj => (hgs j hj).2.2.1)
    tabs_cgi tabPT (by rw [← hR]; exact hhP) po_spec.1 po_spec.2
  have hA := TTc (k := 0) (by norm_num)
  have hP := base.2.2.2.2.2.2.1
  have e : pairCheck = pairCheckAux (threeTbl 0) threeRow₁.centGens.toArray
      (threeRow₁.centGens.toArray.map (invT 275)) (hRec 275 9 RK.cnt RK.T RK.PL)
      (hRec 275 9 PO.cnt PO.T PO.PL) := by
    rw [← hM.1, ← hC.1]
    rfl
  rw [e]
  unfold pairCheckAux
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hC.2.1⟩, hC.2.2⟩, ?_⟩, ?_⟩
  · rw [tabTT (by norm_num), fixedPtCount_eq hA, hfix]
    rfl
  · rw [tabPT]
    exact permOK_unpack hP perm_parts.2.2.2
  · rw [tabPT, sift_eq hP]
    exact hsift
  · rw [tabPT, tabTT (by norm_num), commTT_unpack hP hA, hcomm]
    exact Nat.beq_refl _
  · rw [tabPT, tabTT (by norm_num), pairSel_eq hA hP]
    exact hsel
  · rw [cg_eq, Array.all_eq_true]
    intro j hj
    have hj3 : j < 3 := by simpa using hj
    interval_cases j
    · exact cg_ok (j := 0) (by norm_num)
    · exact cg_ok (j := 1) (by norm_num)
    · exact cg_ok (j := 2) (by norm_num)
  · rw [hRec_size, hPc]
    rfl
  · exact all_hRec fun i hi => rk_sel_mem hi

end CertificateChecks.KernelMcLAS

end
