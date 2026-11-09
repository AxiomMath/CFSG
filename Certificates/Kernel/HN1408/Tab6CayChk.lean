module

public import Certificates.Kernel.HN1408.Tab6CayData
public import Certificates.Kernel.HN1408.Tab6CayDefs
public import Certificates.Kernel.HN1408.CayleyDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Check
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CyRecH
public import Certificates.Kernel.HN1408.SpecDefs
import Certificates.Kernel.HN1408.Spec

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

@[expose] noncomputable def cyHdS (st : List (List (Nat × Nat))) (GW : List Nat) (m cap : Nat)
    (G GI GJ T PL : Nat → Nat) (cnt : Nat) : Bool :=
  bAnd(allN st.length fun j => bAnd(Nat.beq (GI j) (specK GW (st.getD j [])),
    bAnd(Nat.beq (G j) idK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) (GJ j),
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j)))),
    bAnd(Nat.beq cnt m, penumHdK idK cnt cap T PL))

theorem cyHd_of_cyHdS {gs : List (List Nat)} (hgs : ∀ w ∈ gs, lettersOK w = true)
    {st : List (List (Nat × Nat))} {m cap cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (h : cyHdS st (gs.map WK) m cap G GI GJ T PL cnt = true) :
    cyHd (st.map (specWord gs)) m cap G GI GJ T PL cnt = true := by
  have e : ∀ j, WK ((st.map (specWord gs)).getD j []) = specK (gs.map WK) (st.getD j []) := by
    intro j
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases st[j]? with
    | none => rfl
    | some s => exact WK_specWord hgs s
  unfold cyHdS at h
  unfold cyHd
  simp only [List.length_map, e]
  exact h

theorem classaz_letters : ∀ w ∈ classaz.centGens, lettersOK w = true := by decide

theorem ch441694_h2S : cyHdS tab6Row2.stab (classaz.centGens.map WK) 48 tab6Cap Tab6S2.G
    Tab6S2.GI Tab6S2I Tab6S2.T Tab6S2.PL Tab6S2.cnt = true := by quickRfl
theorem ch441694_h4S : cyHdS tab6Row4.stab (classaz.centGens.map WK) 32 tab6Cap Tab6S4.G
    Tab6S4.GI Tab6S4I Tab6S4.T Tab6S4.PL Tab6S4.cnt = true := by quickRfl
theorem ch441694_h6S : cyHdS tab6Row6.stab (classaz.centGens.map WK) 20 tab6Cap Tab6S6.G
    Tab6S6.GI Tab6S6I Tab6S6.T Tab6S6.PL Tab6S6.cnt = true := by quickRfl
theorem ch441694_h7S : cyHdS tab6Row7.stab (classaz.centGens.map WK) 16 tab6Cap Tab6S7.G
    Tab6S7.GI Tab6S7I Tab6S7.T Tab6S7.PL Tab6S7.cnt = true := by quickRfl

theorem ch441694_h2 : cyHd (tab6Row2.stabWords classaz.centGens) 48 tab6Cap Tab6S2.G Tab6S2.GI
    Tab6S2I Tab6S2.T Tab6S2.PL Tab6S2.cnt = true := cyHd_of_cyHdS classaz_letters ch441694_h2S
theorem ch441694_h4 : cyHd (tab6Row4.stabWords classaz.centGens) 32 tab6Cap Tab6S4.G Tab6S4.GI
    Tab6S4I Tab6S4.T Tab6S4.PL Tab6S4.cnt = true := cyHd_of_cyHdS classaz_letters ch441694_h4S
theorem ch441694_h6 : cyHd (tab6Row6.stabWords classaz.centGens) 20 tab6Cap Tab6S6.G Tab6S6.GI
    Tab6S6I Tab6S6.T Tab6S6.PL Tab6S6.cnt = true := cyHd_of_cyHdS classaz_letters ch441694_h6S
theorem ch441694_h7 : cyHd (tab6Row7.stabWords classaz.centGens) 16 tab6Cap Tab6S7.G Tab6S7.GI
    Tab6S7I Tab6S7.T Tab6S7.PL Tab6S7.cnt = true := cyHd_of_cyHdS classaz_letters ch441694_h7S

theorem ch441694_r2H : cyRecC (tab6Row2.stabWords classaz.centGens).length Tab6S2.G Tab6S2.GI
    Tab6S2I Tab6S2.T Tab6S2.PL Tab6S2.POS Tab6S2.SRT Tab6S2.SRI Tab6S2.HS Tab6S2.HSI Tab6S2H Tab6S2Cl
    Tab6S2.cnt = true := by quickRfl
theorem ch441694_r4H : cyRecC (tab6Row4.stabWords classaz.centGens).length Tab6S4.G Tab6S4.GI
    Tab6S4I Tab6S4.T Tab6S4.PL Tab6S4.POS Tab6S4.SRT Tab6S4.SRI Tab6S4.HS Tab6S4.HSI Tab6S4H Tab6S4Cl
    Tab6S4.cnt = true := by quickRfl
theorem ch441694_r6H : cyRecC (tab6Row6.stabWords classaz.centGens).length Tab6S6.G Tab6S6.GI
    Tab6S6I Tab6S6.T Tab6S6.PL Tab6S6.POS Tab6S6.SRT Tab6S6.SRI Tab6S6.HS Tab6S6.HSI Tab6S6H Tab6S6Cl
    Tab6S6.cnt = true := by quickRfl
theorem ch441694_r7H : cyRecC (tab6Row7.stabWords classaz.centGens).length Tab6S7.G Tab6S7.GI
    Tab6S7I Tab6S7.T Tab6S7.PL Tab6S7.POS Tab6S7.SRT Tab6S7.SRI Tab6S7.HS Tab6S7.HSI Tab6S7H Tab6S7Cl
    Tab6S7.cnt = true := by quickRfl

theorem ch441694_r2 : cyRec (tab6Row2.stabWords classaz.centGens).length Tab6S2.G Tab6S2.GI Tab6S2I
    Tab6S2.T Tab6S2.PL Tab6S2.POS Tab6S2.SRT Tab6S2.SRI Tab6S2.HS Tab6S2.HSI Tab6S2Cl Tab6S2.cnt =
    true := cyRec_of_cyRecH (cyRecH_of_cyRecC ch441694_r2H)
theorem ch441694_r4 : cyRec (tab6Row4.stabWords classaz.centGens).length Tab6S4.G Tab6S4.GI Tab6S4I
    Tab6S4.T Tab6S4.PL Tab6S4.POS Tab6S4.SRT Tab6S4.SRI Tab6S4.HS Tab6S4.HSI Tab6S4Cl Tab6S4.cnt =
    true := cyRec_of_cyRecH (cyRecH_of_cyRecC ch441694_r4H)
theorem ch441694_r6 : cyRec (tab6Row6.stabWords classaz.centGens).length Tab6S6.G Tab6S6.GI Tab6S6I
    Tab6S6.T Tab6S6.PL Tab6S6.POS Tab6S6.SRT Tab6S6.SRI Tab6S6.HS Tab6S6.HSI Tab6S6Cl Tab6S6.cnt =
    true := cyRec_of_cyRecH (cyRecH_of_cyRecC ch441694_r6H)
theorem ch441694_r7 : cyRec (tab6Row7.stabWords classaz.centGens).length Tab6S7.G Tab6S7.GI Tab6S7I
    Tab6S7.T Tab6S7.PL Tab6S7.POS Tab6S7.SRT Tab6S7.SRI Tab6S7.HS Tab6S7.HSI Tab6S7Cl Tab6S7.cnt =
    true := cyRec_of_cyRecH (cyRecH_of_cyRecC ch441694_r7H)

theorem ch441694_c2 : cayK t6Mul2 24 [47, 22, 40] (tab6Row2.stabWords classaz.centGens).length
    Tab6S2.cnt Tab6S2.PL Tab6S2Cl (cayCodes t6Mul2 24 [47, 22, 40] Tab6S2.PL Tab6S2.cnt) = true := by
  quickRfl
theorem ch441694_c4 : cayK t6Mul4 0 [10, 1, 20, 15] (tab6Row4.stabWords classaz.centGens).length
    Tab6S4.cnt Tab6S4.PL Tab6S4Cl (cayCodes t6Mul4 0 [10, 1, 20, 15] Tab6S4.PL Tab6S4.cnt) =
    true := by quickRfl
theorem ch441694_c6 : cayK t6Mul6 0 [19, 2, 18] (tab6Row6.stabWords classaz.centGens).length
    Tab6S6.cnt Tab6S6.PL Tab6S6Cl (cayCodes t6Mul6 0 [19, 2, 18] Tab6S6.PL Tab6S6.cnt) = true := by
  quickRfl
theorem ch441694_c7 : cayK t6Mul7 0 [6, 9, 1] (tab6Row7.stabWords classaz.centGens).length
    Tab6S7.cnt Tab6S7.PL Tab6S7Cl (cayCodes t6Mul7 0 [6, 9, 1] Tab6S7.PL Tab6S7.cnt) = true := by
  quickRfl

end CFSG.KD.HN1408.Tab6

end
