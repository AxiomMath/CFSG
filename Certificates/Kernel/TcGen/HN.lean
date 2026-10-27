module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Data.Kernel.SporSch.LyMat
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HNFiveData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false

#lay_seeds CertificateChecks.KernelTc.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

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

theorem tc3_K : seedsP HNThree.tcNregs HNThree.tcProg HNThree.tcSpec.facts HNThree.tcSpec.rA
    HNThree.tcSpec.rB = true := by
  quickRfl

theorem cp3_K : seedsP HNThree.cpNregs HNThree.cpProg HNThree.cpSpec.facts HNThree.cpSpec.rA
    HNThree.cpSpec.rB = true := by
  quickRfl

theorem tc5_K : seedsP HNFive.tcNregs HNFive.tcProg HNFive.tcSpec.facts HNFive.tcSpec.rA
    HNFive.tcSpec.rB = true := by
  quickRfl

theorem cp5_K : seedsP HNFive.cpNregs HNFive.cpProg HNFive.cpSpec.facts HNFive.cpSpec.rA
    HNFive.cpSpec.rB = true := by
  quickRfl

theorem eq_neg : (!seedsP 2 [] [.eq [(0, 1)] [(1, 1)]] 0 1) = true := by
  quickRfl

theorem seed_neg : (!seedsP 2 [] [] 1 0) = true := by
  quickRfl

end CertificateChecks.KernelTc.HN

end
