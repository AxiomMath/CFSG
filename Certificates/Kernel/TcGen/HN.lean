module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Data.Kernel.SporSch.LyMat
public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Data.Kernel.OpsLayTab
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnaps
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNFiveData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNThreeData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNFiveData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false

#lay_seeds CertificateChecks.KernelTc.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

#lay_snaps CertificateChecks.KernelTc.HN.T3 5 133 CertificateChecks.KernelTc.HN.A
  CertificateChecks.KernelTc.HN.B CFSG.AGLEmbedding.R3.HNThree.tcProg 37 100
#lay_snaps CertificateChecks.KernelTc.HN.C3 5 133 CertificateChecks.KernelTc.HN.A
  CertificateChecks.KernelTc.HN.B CFSG.AGLEmbedding.R3.HNThree.cpProg 22 100
#lay_snaps CertificateChecks.KernelTc.HN.T5 5 133 CertificateChecks.KernelTc.HN.A
  CertificateChecks.KernelTc.HN.B CFSG.AGLEmbedding.R3.HNFive.tcProg 38 100
#lay_snaps CertificateChecks.KernelTc.HN.C5 5 133 CertificateChecks.KernelTc.HN.A
  CertificateChecks.KernelTc.HN.B CFSG.AGLEmbedding.R3.HNFive.cpProg 22 100

public section

namespace CertificateChecks.KernelTc.HN

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KC.LQT CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

noncomputable abbrev O5 : Ops Nat Nat :=
  opsFpK lay.p lay.w lay.S lay.d lay.T lay.L lay.H lay.CM lay.RM lay.ONE

@[expose] noncomputable def seedsP (n : Nat) (prog : List Op) (fs : List MFact)
    (rA rB : Nat) : Bool :=
  regsN O5 A B n prog fun R => certN O5 R ⟨n, prog, fs⟩ && O5.eq (getN R rA) A &&
    O5.eq (getN R rB) B

theorem pay_K : (Nat.beq (CFSG.KS.SporSch.LyM.payRunP 5 133 lay.w lay.S LA 0 0 0) A &&
    Nat.beq (CFSG.KS.SporSch.LyM.payRunP 5 133 lay.w lay.S LB 0 0 0) B &&
    validM 5 (133 * lay.S) lay.L lay.H A && validM 5 (133 * lay.S) lay.L lay.H B) = true := by
  quickRfl

@[expose] noncomputable def tabC (i : Nat) : Bool :=
  CFSG.KC.OpsLayTab.tabT O5 C5.VT C5.KT C5.N (3 + i * 32) 32

#kc_each tabC 0 64

@[expose] noncomputable def symP (prog : List Op) (VS : List Nat) (I0 IF : Nat) (S : List Nat)
    (n : Nat) : Bool :=
  CFSG.KC.OpsLayTab.symT C5.KT C5.N n prog VS I0 IF &&
    CFSG.KC.OpsLayK.eqL (CFSG.KC.OpsLayTab.regsT C5.VT n I0) (initN O5 A B n) &&
    CFSG.KC.OpsLayK.eqL (CFSG.KC.OpsLayTab.regsT C5.VT n IF) S

@[expose] noncomputable def factsP (R : List Nat) (n : Nat) (fs : List MFact) (k i : Nat) : Bool :=
  ((fs.drop (i * k)).take k).all (factN O5 R n)

@[expose] noncomputable def seedRegsP (R : List Nat) (rA rB : Nat) : Bool :=
  O5.eq (getN R rA) A && O5.eq (getN R rB) B

@[expose] noncomputable def tc3Fa (i : Nat) : Bool :=
  factsP (T3.SL.getD 12 []) HNThree.tcNregs HNThree.tcSpec.facts 12 i

theorem tc3Sym :
    symP HNThree.tcProg T3.VS T3.I0 T3.IF (T3.SL.getD 12 []) HNThree.tcNregs = true := by
  quickRfl

#kc_each tc3Fa 0 14

theorem tc3Seeds : seedRegsP (T3.SL.getD 12 []) HNThree.tcSpec.rA HNThree.tcSpec.rB = true := by
  quickRfl

@[expose] noncomputable def cp3Fa (i : Nat) : Bool :=
  factsP (C3.SL.getD 10 []) HNThree.cpNregs HNThree.cpSpec.facts 12 i

theorem cp3Sym :
    symP HNThree.cpProg C3.VS C3.I0 C3.IF (C3.SL.getD 10 []) HNThree.cpNregs = true := by
  quickRfl

#kc_each cp3Fa 0 6

theorem cp3Seeds : seedRegsP (C3.SL.getD 10 []) HNThree.cpSpec.rA HNThree.cpSpec.rB = true := by
  quickRfl

@[expose] noncomputable def tc5Fa (i : Nat) : Bool :=
  factsP (T5.SL.getD 12 []) HNFive.tcNregs HNFive.tcSpec.facts 12 i

theorem tc5Sym :
    symP HNFive.tcProg T5.VS T5.I0 T5.IF (T5.SL.getD 12 []) HNFive.tcNregs = true := by
  quickRfl

#kc_each tc5Fa 0 31

theorem tc5Seeds : seedRegsP (T5.SL.getD 12 []) HNFive.tcSpec.rA HNFive.tcSpec.rB = true := by
  quickRfl

@[expose] noncomputable def cp5Fa (i : Nat) : Bool :=
  factsP (C5.SL.getD 10 []) HNFive.cpNregs HNFive.cpSpec.facts 12 i

theorem cp5Sym :
    symP HNFive.cpProg C5.VS C5.I0 C5.IF (C5.SL.getD 10 []) HNFive.cpNregs = true := by
  quickRfl

#kc_each cp5Fa 0 14

theorem cp5Seeds : seedRegsP (C5.SL.getD 10 []) HNFive.cpSpec.rA HNFive.cpSpec.rB = true := by
  quickRfl

theorem ch_neg : (!CFSG.KC.OpsLayTab.symT C5.KT C5.N HNThree.cpNregs (HNThree.cpProg.take 20)
    (C3.VS.drop 1) C3.I0 C3.I0) = true := by
  quickRfl

theorem tab_neg : (!CFSG.KC.OpsLayTab.entT O5 C5.VT (0, 2, 2) 0) = true := by
  quickRfl

theorem eq_neg : (!seedsP 2 [] [.eq [(0, 1)] [(1, 1)]] 0 1) = true := by
  quickRfl

theorem seed_neg : (!seedsP 2 [] [] 1 0) = true := by
  quickRfl

end CertificateChecks.KernelTc.HN

end
