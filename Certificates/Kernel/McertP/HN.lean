module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayMcert
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData5
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaHNData
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

#lay_seeds CertificateChecks.KernelMP.HN 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

public section

namespace CertificateChecks.KernelMP.HN

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHN

theorem hn7_K : mcertL lay A B ⟨hn_7_claims.nregs, hn_7_claims.prog, hn_7_claims.facts⟩ = true := by
  decide +kernel

theorem hn7_wf : hn_7_claims.wf = true := by decide +kernel

theorem alpha_K : mcertL lay A B ⟨hnNregs, hnProg, hnMod.modFactsE 3 hnTops hnGs⟩ = true := by
  decide +kernel

theorem alpha_restA : (hnMod.wf 3 && pcWf (hnTops ++ hnMod.basisPc 3) &&
    hnMod.acts.all (fun g => g.mat.all (· < 3)) &&
    hnTops.all (fun q => hnMod.acts.any (·.reg == q.reg))) = true := by
  decide +kernel

theorem alpha_grp : hnMod.grpOK hnTops hnGs = true := by decide +kernel

theorem alpha_rank : decide (3 ≤ hnMod.basis.length) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem alpha_fun : hnMod.funOK 3 hnCf = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem alpha_alt : hnMod.altOK 3 hnCi hnCt tgtAlt = true := by decide +kernel

theorem hn7_neg : (!mcertL lay B A ⟨hn_7_claims.nregs, hn_7_claims.prog, hn_7_claims.facts⟩) =
    true := by
  decide +kernel

theorem alpha_neg : (!mcertL lay B A ⟨hnNregs, hnProg, hnMod.modFactsE 3 hnTops hnGs⟩) = true := by
  decide +kernel

end CertificateChecks.KernelMP.HN

end
