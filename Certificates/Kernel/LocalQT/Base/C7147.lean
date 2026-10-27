module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import CFSG.Quasithin.Vol2.KGFactRankRuData
public import Certificates.Kernel.LocalQT.Base.C7147C
public import Certificates.Kernel.LocalQT.Base.C7147T
public import Certificates.Kernel.LocalQT.Base.C7147A
public import Certificates.Kernel.LocalQT.Base.C7147B
public import Certificates.Kernel.LocalQT.Base.C4076
public import CFSG.Certificates.Kernel.LocalQTTreeRSound
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermK1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank
public import CFSG.Certificates.Kernel.Common.ForallTree
import Certificates.Data.CFSGNative.Ru.Data

set_option maxRecDepth 100000

public section

#kc_forall_tree CFSG.KD.LQT.C7147.ch7147_all
  (fun k => CFSG.KC.LQT.TR.childR 15 3 16384 338 CFSG.KD.LQT.C4076.PT CFSG.KD.LQT.C4076.CT
    CFSG.Quasithin.H13.KGRank.ruRankNodes CFSG.KD.LQT.C7147.cand k = true) 14
  CFSG.KD.LQT.C7147.ch7147c

namespace CFSG.KD.LQT.C7147

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.QuasithinUnique.Lin2.RankCert CFSG.Quasithin.H13.KGRank CFSG.KC.LQT.TR CFSG.KC.LQT.RB
open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

theorem treeR : treeRT 15 3 16384 338 C4076.PT C4076.CT ruRankNodes = true :=
  CFSG.KC.LQT.TR.Pf.treeRT_of_split cnd top ch7147_all

theorem cen : ∀ i < ruEnum.1.size, mulIdx 3 3 ruEnum.2.1 ruEnum.2.2 ruEnum.1.size 338 i =
    mulIdx 3 3 ruEnum.2.1 ruEnum.2.2 ruEnum.1.size i 338 := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have ha : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
    simp [ruTa]
  have hb : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
    simp [ruTb]
  have hcert : BaseCertS ruData.n ruB (slpTabsA (tab ruData.n (a ruData)).toArray
      (tab ruData.n (b ruData)).toArray ruProg) ruQp 154 187 191 189 193 ruEnum.1 ruEnum.2.1
      ruEnum.2.2 14 := by
    rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
    exact C4143.cert
  obtain ⟨-, -, hEnum, -⟩ := A5.Kc3SporPerm.baseCertS_data ruB (base_lt hF) (base_property hF)
    (a ruData) (b ruData) ruProg C4143.valid ruQp 154 187 191 189 193 _ _ _ 14 hcert
  obtain ⟨ι, hcay, -⟩ := exists_cayley_of_baseEnum (base_lt hF) (base_property hF) _ _ _ _ hEnum
  rw [List.length_map] at hcay
  have hf := C4076.check
  rw [FusionCert.fusionCheck] at hf
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    List.length_map] at hf
  obtain ⟨⟨⟨⟨⟨⟨hzi, -⟩, -⟩, hgen⟩, -⟩, -⟩, -⟩ := hf
  have hq : ruQp.length = 3 := rfl
  have hz : ruZI = 338 := rfl
  rw [hq] at hcay hgen
  rw [hz] at hzi hgen
  exact CFSG.KC.LQT.TR.Pf.cen_of_cayley hcay hzi hgen

theorem tree :
    treeCheck ruEnum.1.size ruQp.length ruQp.length ruEnum.2.1 ruEnum.2.2 338 ruRankNodes =
      true := by
  have hc := cen
  have hq : ruQp.length = 3 := rfl
  rw [hq]
  revert hc
  unfold ruEnum ruSLP
  rw [C4143.n_eq, C4143.ta_eq, C4143.tb_eq]
  intro hc
  obtain ⟨-, -, -, -, -, hparlt, hcllt, hX⟩ := CFSG.KC.LQT.BSP.bfsS_enum (hw := by norm_num)
    (h := C4143.hd) (hnd := C4143.N.all) (hs := C4143.S.all) (hb := C4076.B.all)
    (hcov := by norm_num)
  have hX' := hX _ rfl
  clear hX
  generalize bfsEnumB 4060 ruB
    (ruQp.map fun p => (slpTabsA C4143.ta.toArray C4143.tb.toArray ruProg)[p.1]!)
    (ruQp.map fun p => (slpTabsA C4143.ta.toArray C4143.tb.toArray ruProg)[p.2]!) 100000 = X
    at hX' hc ⊢
  obtain ⟨hXs, -, hX2, hX3⟩ := hX'
  rw [hXs] at hc ⊢
  have hfP : ∀ i < 16384, 0 < i → fieldT 15 C4076.PT i = X.2.1[i]! :=
    fun i hi h0 => (hX2 i hi h0).symm
  have hfC : ∀ i < 16384, ∀ j < 3, fieldT 15 C4076.CT (i * (3 + 3) + j) =
      X.2.2[i * (3 + 3) + j]! := fun i hi j hj => (hX3 i hi j hj).symm
  have hpar : ∀ i < 16384, 0 < i → X.2.1[i]! < i ∧ 0 < 3 := fun i hi h0 => by
    rw [← hfP i hi h0]
    exact hparlt i hi h0
  have hcl : ∀ i < 16384, ∀ j < 3, X.2.2[i * (3 + 3) + j]! < 16384 := fun i hi j hj => by
    rw [← hfC i hi j hj]
    exact hcllt i hi j hj
  exact CFSG.KC.LQT.TR.Pf.treeR_sound hfP hfC hpar hcl
    (CFSG.KC.LQT.TR.Pf.cen_mulT hfP hfC hpar hcl (by norm_num) hc) treeR

end CFSG.KD.LQT.C7147

end
