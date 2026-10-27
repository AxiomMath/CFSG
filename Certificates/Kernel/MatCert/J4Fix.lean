module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.MatCert.J4Seeds
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Data
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData6
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem j4Fix_K : regsN (opsF2K 112) JA.M JB.M j4Nregs j4Prog
    (fun R => certN (opsF2K 112) R ⟨j4Nregs, j4Prog, j4Spec.facts⟩ &&
      (opsF2K 112).eq (getN R j4Spec.rA) JA.M && (opsF2K 112).eq (getN R j4Spec.rB) JB.M) =
    true := by
  quickRfl

theorem j4Sec_K : mcertN (opsF2K 112) JA.M JB.M
    ⟨j4_7_claims.nregs, j4_7_claims.prog, j4_7_claims.facts⟩ = true := by
  quickRfl

theorem j4Sec_neg : (!mcertN (opsF2K 112) JA.M JB.M ⟨2, [], [.eq [(0, 1)] [(1, 1)]]⟩) = true := by
  quickRfl

theorem j4Fix_neg : (!mcertN (opsF2K 112) JA.M JB.M ⟨2, [], [.ne [(0, 1)] [(0, 1)] 0]⟩) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
