module

public import Certificates.Kernel.MatCert.HN11.Steps
public import Certificates.Kernel.MatCert.HN11.Tabs
public import Certificates.Data.Kernel.LocalComp.FactsV
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigData7
import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMC.HN11

open CFSG.KC.LocalComp.FactsV CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.KD.MC.HN11 (lay V P N)

theorem regs_K : regsV lay V P TT N hn_11_claims.nregs hn_11_claims.prog RF = true := by
  quickRfl

@[expose] noncomputable def chk (i : Nat) : Bool :=
  chunkV lay V P N RF hn_11_claims.nregs hn_11_claims.facts HH (fun _ => true) 256 i

theorem nfacts : hn_11_claims.facts.length ≤ 14 * 256 := by decide +kernel

end CertificateChecks.KernelMC.HN11

#kc_each CertificateChecks.KernelMC.HN11.chk 0 14

namespace CertificateChecks.KernelMC.HN11

open CFSG.KC.LocalComp.FactsV CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.KD.MC.HN11 (lay V P N)

theorem neg_regs : Bool.not (regsV lay V P (fun s => TT (s + 1)) N hn_11_claims.nregs
    hn_11_claims.prog RF) = true := by quickRfl

theorem neg_facts : Bool.not (chunkV lay V P N RF hn_11_claims.nregs hn_11_claims.facts
    (fun i => HH (i + 1)) (fun _ => true) 256 0) = true := by quickRfl

end CertificateChecks.KernelMC.HN11

end
