module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.LocalComp.ThOrder
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3

theorem thTz_K : regsN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN thThreeProg
    (fun R => certN (opsF2K 248) R ⟨thThreeN, thThreeProg, thTzSpec.facts⟩ &&
      (opsF2K 248).eq (getN R 0) KernelLC.ThA.M && (opsF2K 248).eq (getN R 1) KernelLC.ThB.M) =
    true := by
  quickRfl

theorem thCz_K : regsN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thThreeN thThreeProg
    (fun R => certN (opsF2K 248) R ⟨thThreeN, thThreeProg, thCzSpec.facts⟩ &&
      (opsF2K 248).eq (getN R 0) KernelLC.ThA.M && (opsF2K 248).eq (getN R 1) KernelLC.ThB.M) =
    true := by
  quickRfl

theorem thTz_neg : (!regsN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M 2 []
    (fun R => (opsF2K 248).eq (getN R 0) KernelLC.ThB.M)) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
