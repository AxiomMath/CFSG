module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Data.Kernel.OpsLayMcert
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLyData
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

#lay_seeds CertificateChecks.KernelMP.Ly 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

public section

namespace CertificateChecks.KernelMP.Ly

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLy

theorem ly31_K : mcertL lay A B ⟨2, [], ly_31_claims.baseFacts⟩ = true := by decide +kernel

theorem ly31_wf : ly_31_claims.wf = true := by decide +kernel

theorem ly7_K : mcertL lay A B ⟨ly_7_claims.nregs, ly_7_claims.prog, ly_7_claims.facts⟩ = true := by
  decide +kernel

theorem ly7_wf : ly_7_claims.wf = true := by decide +kernel

theorem alpha_K : mcertL lay A B ⟨lyNregs, lyProg, lyMod.modFactsW 3 lyTops⟩ = true := by
  decide +kernel

theorem alpha_restA : (lyMod.wf 3 && pcWf (lyTops ++ lyMod.basisPc 3) &&
    lyTops.all (fun q => lyMod.acts.any (·.reg == q.reg))) = true := by
  decide +kernel

theorem alpha_wTops : lyTidx.all (fun i => decide (i < lyMod.acts.length) &&
    lyTops.any (·.reg == (lyMod.acts.getD i default).reg)) = true := by
  decide +kernel

theorem alpha_wNodup : ((wordsL 3 lyMod.basis.length
    (lyTidx.map fun i => (lyMod.acts.getD i default).mat)).map (codeL 3)).Nodup := by
  decide +kernel

theorem alpha_wCount : decide (3 ^ 7 ≤ (wordsL 3 lyMod.basis.length
    (lyTidx.map fun i => (lyMod.acts.getD i default).mat)).length * 3 ^ lyMod.basis.length) =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem alpha_restB : (decide (3 ≤ lyMod.basis.length) && lyMod.funOK 3 lyCf &&
    lyMod.altOK 3 lyCi lyCt tgtAlt) = true := by
  decide +kernel

theorem ly31_neg : (!mcertL lay B A ⟨2, [], ly_31_claims.baseFacts⟩) = true := by decide +kernel

theorem ly7_neg : (!mcertL lay B A ⟨ly_7_claims.nregs, ly_7_claims.prog, ly_7_claims.facts⟩) =
    true := by
  decide +kernel

theorem alpha_neg : (!mcertL lay B A ⟨lyNregs, lyProg, lyMod.modFactsW 3 lyTops⟩) = true := by
  decide +kernel

end CertificateChecks.KernelMP.Ly

end
