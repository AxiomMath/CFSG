module

public import Certificates.Kernel.TcGen.HN
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsFpKSound
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
      (by decide +kernel) (by decide +kernel) HN.tc5_K,
    cpP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) HN.cp5_K,
    by decide +kernel⟩

theorem cert9506 :
    (tcCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 HNThree.tcNregs
      HNThree.tcProg HNThree.tcSpec = true) ∧
    (cpCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 HNThree.cpNregs
      HNThree.cpProg HNThree.cpSpec = true) ∧ (HNThree.cpSpec.noFun = true) :=
  ⟨tcP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) HN.tc3_K,
    cpP_of HN.consts (by decide) HN.rowsA HN.rowsB HN.pay.2.2.1 HN.pay.2.2.2 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) HN.cp3_K,
    by decide +kernel⟩

end CertificateChecks.KernelTc

end
