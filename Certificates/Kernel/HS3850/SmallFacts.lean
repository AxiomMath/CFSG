module

public import Certificates.Kernel.HS3850.Kit
public import Certificates.Data.SolMaxH35HS
public import Certificates.Data.GrSLitL34FactsCF23SocHSCheck
public import Certificates.Kernel.LocalQT.HSAut.F4146

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KD.LQT.HO CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.QuasithinUnique.Id2519.HSAut

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem cIdn' : Cn idn := cIdn

theorem dTab_eq : CFSG.ComponentClassification.SolMax.H35.HS.dTab =
    unpack 3850 12 (wfoldR lc2 [0, 0, 1, 0]) ∧ Cn (wfoldR lc2 [0, 0, 1, 0]) := by
  have e : CFSG.ComponentClassification.SolMax.H35.HS.dTab = wordTabS 3850 hsC2Tabs [0, 0, 1, 0] := by
    unfold CFSG.ComponentClassification.SolMax.H35.HS.dTab hsDGens
    rw [getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
    rfl
  rw [e]
  exact c2Word (by decide)

theorem t2Tab_eq : CFSG.ComponentClassification.GSThmB.CovHS.t2Tab = unpack 3850 12 (HC.F 12) :=
  (cent_parts (by norm_num)).1

theorem hsH35Check_true : CFSG.ComponentClassification.SolMax.H35.HS.hsH35Check = true := by
  obtain ⟨hd, cd⟩ := dTab_eq
  have c12 := (cent_parts (k := 12) (by norm_num)).2
  have h := ok23300
  rw [CFSG.KS.PEnum.strictB_app'] at h
  obtain ⟨h1, h2, h3⟩ := by simpa only [bAnd_iff] using h
  unfold CFSG.ComponentClassification.SolMax.H35.HS.hsH35Check
  rw [hd, t2Tab_eq, comp_pc' cd cd, idTab_idn, beq_pc' (cn_pc cd cd) cIdn', beq_pc' cd cIdn',
    comp_pc' c12 cd, fixedCount_fx, beq_true h1, beq_true h3, Nat.beq_refl]
  simp [h2]

theorem e_parts : e1Tab = unpack 3850 12 (wfoldR lq e1Letters) ∧ Cn (wfoldR lq e1Letters) ∧
    e2Tab = unpack 3850 12 (wfoldR lq e2Letters) ∧ Cn (wfoldR lq e2Letters) :=
  ⟨(wordE CFSG.KD.LQT.HO.e1Letters_lt).1, (wordE CFSG.KD.LQT.HO.e1Letters_lt).2, (wordE CFSG.KD.LQT.HO.e2Letters_lt).1, (wordE CFSG.KD.LQT.HO.e2Letters_lt).2⟩

theorem hsOrderSixOK_true : CFSG.ComponentClassification.GSThmB.Soc.hsOrderSixOK = true := by
  obtain ⟨he1, ce1, he2, ce2⟩ := e_parts
  have h := ok22228
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have c1 := cn_pc ce1 ce2
  have c2 := cn_pc c1 c1
  have c3 := cn_pc c2 c1
  unfold CFSG.ComponentClassification.GSThmB.Soc.hsOrderSixOK
    CFSG.ComponentClassification.GSThmB.Soc.hsW6 CFSG.ComponentClassification.GSThmB.Soc.hsW3
    CFSG.ComponentClassification.GSThmB.Soc.hsW2 CFSG.ComponentClassification.GSThmB.Soc.hsW1
  rw [he1, he2, comp_pc' ce1 ce2, comp_pc' c1 c1, comp_pc' c2 c1, comp_pc' c3 c3, idTab_idn,
    beq_pc' (cn_pc c3 c3) cIdn', beq_pc' c2 cIdn', beq_pc' c3 cIdn', beq_true h1, Nat.beq_refl]
  simp [h2, h3]

theorem yTab_eq : CFSG.ComponentClassification.GSThmB.CovHS.yTab =
    unpack 3850 12 (wfoldR lc2 [3, 0, 0, 3, 2]) ∧ Cn (wfoldR lc2 [3, 0, 0, 3, 2]) :=
  c2Word (by decide)

theorem kleinCheck_true : CFSG.ComponentClassification.GSThmB.CovHS.kleinCheck = true := by
  obtain ⟨hy, cy⟩ := yTab_eq
  obtain ⟨h5, c5⟩ := cent_parts (k := 5) (by norm_num)
  obtain ⟨h12, c12⟩ := cent_parts (k := 12) (by norm_num)
  have h := ok23004
  simp only [CFSG.KS.PEnum.strictB_app', bAnd_iff] at h
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := h
  have p5 := CFSG.KD.LQT.HN.cent_perm (k := 5) (by norm_num) c5
  have p12 := CFSG.KD.LQT.HN.cent_perm (k := 12) (by norm_num) c12
  have s5 := CFSG.KD.LQT.HN.cent_size (k := 5) (by norm_num)
  have s12 := CFSG.KD.LQT.HN.cent_size (k := 12) (by norm_num)
  unfold CFSG.ComponentClassification.GSThmB.CovHS.kleinCheck
    CFSG.ComponentClassification.GSThmB.CovHS.t1Tab
  rw [t2Tab_eq, hy, h5, comp_pc' cy cy, comp_pc' c12 cy, idTab_idn,
    beq_pc' (cn_pc cy cy) cIdn', beq_pc' cy cIdn', fixedCount_fx, fixedCount_fx, fixedCount_fx,
    fixedCount_fx, beq_true f1, beq_true f2, beq_true f3, beq_true f5, beq_true f6, Nat.beq_refl,
    ← h5, ← t2Tab_eq]
  simp [p5, p12, f4, CFSG.ComponentClassification.GSThmB.CovHS.yWord,
    CFSG.ComponentClassification.GSThmB.CovHS.t2Tab, natArr, s5, s12]

end CFSG.KD.HS3850

end
