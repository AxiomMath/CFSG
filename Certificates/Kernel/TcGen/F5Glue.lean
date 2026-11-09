module

public import Certificates.Kernel.TcGen.HN
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsFpKSound
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.Certificates.Kernel.OpsLayTabSound
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KC.LQT CFSG.KS.SporSch.LyM
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint

theorem tcP_of {p w S d T L H CM RM ONE LV HV A B : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 0 < d) {sA sB : String}
    (eA : (opsP p d).decode sA = unpackL d w S A) (eB : (opsP p d).decode sB = unpackL d w S B)
    (hA : validM p (d * S) L H A = true) (hB : validM p (d * S) L H B = true) {n : Nat}
    {prog : List Op} {D : TSpec} (hrA : D.rA < n) (hrB : D.rB < n) (hw : D.wf = true)
    (h : regsN (opsFpK p w S d T L H CM RM ONE) A B n prog
      (fun R => certN (opsFpK p w S d T L H CM RM ONE) R ⟨n, prog, D.facts⟩ &&
        (opsFpK p w S d T L H CM RM ONE).eq (getN R D.rA) A &&
        (opsFpK p w S d T L H CM RM ONE).eq (getN R D.rB) B) = true) :
    tcCheck (opsP p d) sA sB n prog D = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (homP hc hd) eA eB hA hB (fs := D.facts) hrA hrB h
  unfold tcCheck
  rw [hm, h0, h1, decide_eq_true hrA, decide_eq_true hrB, hw]
  rfl

theorem cpP_of {p w S d T L H CM RM ONE LV HV A B : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hd : 0 < d) {sA sB : String}
    (eA : (opsP p d).decode sA = unpackL d w S A) (eB : (opsP p d).decode sB = unpackL d w S B)
    (hA : validM p (d * S) L H A = true) (hB : validM p (d * S) L H B = true) {n : Nat}
    {prog : List Op} {D : CpSpec} (hrA : D.rA < n) (hrB : D.rB < n) (hw : D.wf = true)
    (h : regsN (opsFpK p w S d T L H CM RM ONE) A B n prog
      (fun R => certN (opsFpK p w S d T L H CM RM ONE) R ⟨n, prog, D.facts⟩ &&
        (opsFpK p w S d T L H CM RM ONE).eq (getN R D.rA) A &&
        (opsFpK p w S d T L H CM RM ONE).eq (getN R D.rB) B) = true) :
    cpCheck (opsP p d) sA sB n prog D = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (homP hc hd) eA eB hA hB (fs := D.facts) hrA hrB h
  unfold cpCheck
  rw [hm, h0, h1, decide_eq_true hrA, decide_eq_true hrB, hw]
  rfl

namespace HN

theorem tab : ∀ v, 2 < v → v < C5.N →
    CFSG.KC.OpsLayTab.entT O5 C5.VT (CFSG.KC.OpsLayTab.keyAt C5.KT v) v = true := by
  refine CFSG.KC.OpsLayTab.tab_of_chunks O5 (m := 64) (k := 32) (by decide) fun i hi => ?_
  interval_cases i
  exacts [tabC0, tabC1, tabC2, tabC3, tabC4, tabC5, tabC6, tabC7, tabC8, tabC9, tabC10, tabC11,
    tabC12, tabC13, tabC14, tabC15, tabC16, tabC17, tabC18, tabC19, tabC20, tabC21, tabC22, tabC23,
    tabC24, tabC25, tabC26, tabC27, tabC28, tabC29, tabC30, tabC31, tabC32, tabC33, tabC34, tabC35,
    tabC36, tabC37, tabC38, tabC39, tabC40, tabC41, tabC42, tabC43, tabC44, tabC45, tabC46, tabC47,
    tabC48, tabC49, tabC50, tabC51, tabC52, tabC53, tabC54, tabC55, tabC56, tabC57, tabC58, tabC59,
    tabC60, tabC61, tabC62, tabC63]

theorem fold_of_symP {prog : List Op} {VS S : List Nat} {I0 IF n : Nat}
    (h : symP prog VS I0 IF S n = true) : prog.foldl (stepL O5) (initN O5 A B n) = S := by
  unfold symP at h
  simp only [Bool.and_eq_true] at h
  rw [← CFSG.KC.OpsLayK.eq_of_eqL h.1.2, CFSG.KC.OpsLayTab.fold_symT O5 tab _ _ _ _ h.1.1,
    CFSG.KC.OpsLayK.eq_of_eqL h.2]

theorem regsF_of {n : Nat} {prog : List Op} {fs : List MFact} {rA rB : Nat} {S : List Nat}
    {kf mf : Nat} (hrun : prog.foldl (stepL O5) (initN O5 A B n) = S) (hn : 2 ≤ n)
    (hp : prog.all (Op.lt n) = true) (hmf : fs.length ≤ mf * kf)
    (hf : ∀ i < mf, factsP S n fs kf i = true) (he : seedRegsP S rA rB = true) :
    regsN O5 A B n prog (fun R => certN O5 R ⟨n, prog, fs⟩ && O5.eq (getN R rA) A &&
      O5.eq (getN R rB) B) = true := by
  rw [regsN_eq, hrun]
  unfold certN seedRegsP at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he ⊢
  exact ⟨⟨⟨⟨hn, hp⟩, CFSG.KC.OpsLayK.all_of_chunks hmf hf⟩, he.1⟩, he.2⟩

theorem tc3Fa_all : ∀ i < 14, tc3Fa i = true := by
  intro i hi
  interval_cases i
  exacts [tc3Fa0, tc3Fa1, tc3Fa2, tc3Fa3, tc3Fa4, tc3Fa5, tc3Fa6, tc3Fa7, tc3Fa8, tc3Fa9, tc3Fa10,
    tc3Fa11, tc3Fa12, tc3Fa13]

theorem cp3Fa_all : ∀ i < 6, cp3Fa i = true := by
  intro i hi
  interval_cases i
  exacts [cp3Fa0, cp3Fa1, cp3Fa2, cp3Fa3, cp3Fa4, cp3Fa5]

theorem tc5Fa_all : ∀ i < 31, tc5Fa i = true := by
  intro i hi
  interval_cases i
  exacts [tc5Fa0, tc5Fa1, tc5Fa2, tc5Fa3, tc5Fa4, tc5Fa5, tc5Fa6, tc5Fa7, tc5Fa8, tc5Fa9, tc5Fa10,
    tc5Fa11, tc5Fa12, tc5Fa13, tc5Fa14, tc5Fa15, tc5Fa16, tc5Fa17, tc5Fa18, tc5Fa19, tc5Fa20,
    tc5Fa21, tc5Fa22, tc5Fa23, tc5Fa24, tc5Fa25, tc5Fa26, tc5Fa27, tc5Fa28, tc5Fa29, tc5Fa30]

theorem cp5Fa_all : ∀ i < 14, cp5Fa i = true := by
  intro i hi
  interval_cases i
  exacts [cp5Fa0, cp5Fa1, cp5Fa2, cp5Fa3, cp5Fa4, cp5Fa5, cp5Fa6, cp5Fa7, cp5Fa8, cp5Fa9, cp5Fa10,
    cp5Fa11, cp5Fa12, cp5Fa13]

theorem consts : constsOK lay.p lay.w lay.S lay.d lay.T lay.L lay.H lay.CM lay.RM lay.ONE lay.LV
    lay.HV = true := lay_ok

theorem pay : payRunP 5 133 lay.w lay.S LA 0 0 0 = A ∧ payRunP 5 133 lay.w lay.S LB 0 0 0 = B ∧
    validM lay.p (lay.d * lay.S) lay.L lay.H A = true ∧
    validM lay.p (lay.d * lay.S) lay.L lay.H B = true := by
  have h := pay_K
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2, h.1.2, h.2⟩

theorem rowsA : (opsP lay.p lay.d).decode NativeSporadic.HNSeed1 = unpackL lay.d lay.w lay.S A := by
  rw [LA_eq]
  change CFSG.Sporadic.He.Native.rowsOf 5 133 (String.ofList LA) = _
  rw [payRunP_eqL (w := lay.w) (S := lay.S) LA (by decide) (by decide) (by decide), pay.1]
  rfl

theorem rowsB : (opsP lay.p lay.d).decode NativeSporadic.HNSeed2 = unpackL lay.d lay.w lay.S B := by
  rw [LB_eq]
  change CFSG.Sporadic.He.Native.rowsOf 5 133 (String.ofList LB) = _
  rw [payRunP_eqL (w := lay.w) (S := lay.S) LB (by decide) (by decide) (by decide), pay.2.1]
  rfl

end HN

theorem cert9505 :
    (tcCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 HNFive.tcNregs
      HNFive.tcProg HNFive.tcSpec = true) ∧
    (cpCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 HNFive.cpNregs
      HNFive.cpProg HNFive.cpSpec = true) ∧ (HNFive.cpSpec.noFun = true) :=
  ⟨tcP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (HN.regsF_of (kf := 12) (HN.fold_of_symP HN.tc5Sym) (by decide) (by decide +kernel)
        (by decide +kernel) HN.tc5Fa_all HN.tc5Seeds),
    cpP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (HN.regsF_of (kf := 12) (HN.fold_of_symP HN.cp5Sym) (by decide) (by decide +kernel)
        (by decide +kernel) HN.cp5Fa_all HN.cp5Seeds),
    by decide +kernel⟩

theorem cert9506 :
    (tcCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 HNThree.tcNregs
      HNThree.tcProg HNThree.tcSpec = true) ∧
    (cpCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 HNThree.cpNregs
      HNThree.cpProg HNThree.cpSpec = true) ∧ (HNThree.cpSpec.noFun = true) :=
  ⟨tcP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (HN.regsF_of (kf := 12) (HN.fold_of_symP HN.tc3Sym) (by decide) (by decide +kernel)
        (by decide +kernel) HN.tc3Fa_all HN.tc3Seeds),
    cpP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (HN.regsF_of (kf := 12) (HN.fold_of_symP HN.cp3Sym) (by decide) (by decide +kernel)
        (by decide +kernel) HN.cp3Fa_all HN.cp3Seeds),
    by decide +kernel⟩

end CertificateChecks.KernelTc

end
