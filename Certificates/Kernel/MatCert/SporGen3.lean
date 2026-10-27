module

public import Certificates.Data.Kernel.OpsMcertB
public import Certificates.Kernel.LocalComp.ThOrder
public import Certificates.Kernel.MatCert.J4Seeds
public import Certificates.Kernel.SectionRankHS.RuSeeds
public import Certificates.Kernel.MatCert.HeringFp
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J2Data
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3HeData
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3RuData
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J4Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenThData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMB CFSG.KC.OpsK CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

theorem sg3Th_K : seedRunB (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thLineCert = true := by
  quickRfl

theorem sg3J2_K : forceB (payJ2 J2S1.chars) (fun A => forceB (payJ2 J2S2.chars) fun B =>
    vldJ2 A && vldJ2 B && seedRunB O5 A B j2Cert) = true := by
  quickRfl

theorem sg3He_K : forceB (payHe HeS1.chars) (fun A => forceB (payHe HeS2.chars) fun B =>
    vldHe A && vldHe B && seedRunB O7 A B heCert) = true := by
  quickRfl

theorem sg3Ru_K : seedRunB (opsF2K 28) KernelSRHS.RA.M KernelSRHS.RB.M ruCert = true := by
  quickRfl

theorem sg3J4_K : seedRunB (opsF2K 112) JA.M JB.M j4Cert = true := by
  quickRfl

end CertificateChecks.KernelMC

end
