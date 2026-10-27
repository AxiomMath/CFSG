module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.LocalComp.M1Gen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co3ThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co2ThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co1FiveData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Co1ThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelTc.C3A CFSG.Blueprint.NativeSporadic.Co3Seed1
#lc_m1 CertificateChecks.KernelTc.C3A CFSG.Blueprint.NativeSporadic.Co3Seed1 22
#ks_chars CertificateChecks.KernelTc.C3B CFSG.Blueprint.NativeSporadic.Co3Seed2
#lc_m1 CertificateChecks.KernelTc.C3B CFSG.Blueprint.NativeSporadic.Co3Seed2 22
#ks_chars CertificateChecks.KernelTc.C2A CFSG.Blueprint.NativeSporadic.Co2Seed1
#lc_m1 CertificateChecks.KernelTc.C2A CFSG.Blueprint.NativeSporadic.Co2Seed1 22
#ks_chars CertificateChecks.KernelTc.C2B CFSG.Blueprint.NativeSporadic.Co2Seed2
#lc_m1 CertificateChecks.KernelTc.C2B CFSG.Blueprint.NativeSporadic.Co2Seed2 22
#ks_chars CertificateChecks.KernelTc.C1A CFSG.Blueprint.NativeSporadic.Co1Seed1
#lc_m1 CertificateChecks.KernelTc.C1A CFSG.Blueprint.NativeSporadic.Co1Seed1 24
#ks_chars CertificateChecks.KernelTc.C1B CFSG.Blueprint.NativeSporadic.Co1Seed2
#lc_m1 CertificateChecks.KernelTc.C1B CFSG.Blueprint.NativeSporadic.Co1Seed2 24

namespace CertificateChecks.KernelTc

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3

@[expose] noncomputable def seedsF2 (d A B n : Nat) (prog : List Op) (fs : List MFact)
    (rA rB : Nat) : Bool :=
  regsN (opsF2K d) A B n prog fun R => certN (opsF2K d) R ⟨n, prog, fs⟩ &&
    (opsF2K d).eq (getN R rA) A && (opsF2K d).eq (getN R rB) B

theorem co3tc_K : seedsF2 22 C3A.M C3B.M Co3Three.tcNregs Co3Three.tcProg Co3Three.tcSpec.facts
    Co3Three.tcSpec.rA Co3Three.tcSpec.rB = true := by
  quickRfl

theorem co3cp_K : seedsF2 22 C3A.M C3B.M Co3Three.cpNregs Co3Three.cpProg Co3Three.cpSpec.facts
    Co3Three.cpSpec.rA Co3Three.cpSpec.rB = true := by
  quickRfl

theorem co2tc_K : seedsF2 22 C2A.M C2B.M Co2Three.tcNregs Co2Three.tcProg Co2Three.tcSpec.facts
    Co2Three.tcSpec.rA Co2Three.tcSpec.rB = true := by
  quickRfl

theorem co2cp_K : seedsF2 22 C2A.M C2B.M Co2Three.cpNregs Co2Three.cpProg Co2Three.cpSpec.facts
    Co2Three.cpSpec.rA Co2Three.cpSpec.rB = true := by
  quickRfl

theorem co1ftc_K : seedsF2 24 C1A.M C1B.M Co1Five.tcNregs Co1Five.tcProg Co1Five.tcSpec.facts
    Co1Five.tcSpec.rA Co1Five.tcSpec.rB = true := by
  quickRfl

theorem co1fcp_K : seedsF2 24 C1A.M C1B.M Co1Five.cpNregs Co1Five.cpProg Co1Five.cpSpec.facts
    Co1Five.cpSpec.rA Co1Five.cpSpec.rB = true := by
  quickRfl

theorem co1ttc_K : seedsF2 24 C1A.M C1B.M Co1Three.tcNregs Co1Three.tcProg
    Co1Three.tcSpec.facts Co1Three.tcSpec.rA Co1Three.tcSpec.rB = true := by
  quickRfl

theorem co1tcp_K : seedsF2 24 C1A.M C1B.M Co1Three.cpNregs Co1Three.cpProg
    Co1Three.cpSpec.facts Co1Three.cpSpec.rA Co1Three.cpSpec.rB = true := by
  quickRfl

theorem co2tc_neg_seeds : (!seedsF2 22 C2B.M C2A.M Co2Three.tcNregs Co2Three.tcProg
    Co2Three.tcSpec.facts Co2Three.tcSpec.rA Co2Three.tcSpec.rB) = true := by
  quickRfl

theorem co3cp_neg_ord : (!seedsF2 22 C3A.M C3B.M Co3Three.cpNregs Co3Three.cpProg
    (.ord 0 2 :: Co3Three.cpSpec.facts) Co3Three.cpSpec.rA Co3Three.cpSpec.rB) = true := by
  quickRfl

theorem co1_neg_ne : (!seedsF2 24 C1A.M C1B.M 2 [] [.ne [(0, 1)] [(0, 1)] 0] 0 1) = true := by
  quickRfl

end CertificateChecks.KernelTc

end
