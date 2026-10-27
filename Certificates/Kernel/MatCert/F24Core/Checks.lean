module

public import Certificates.Kernel.MatCert.F24Core.Steps
public import Certificates.Kernel.MatCert.F24Core.Tabs
public import Certificates.Data.Kernel.LocalComp.FactsV
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreFi24SevenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreSplit
import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMC.F24C

open CFSG.KC.LocalComp.FactsV CFSG.AGLEmbedding.R3 CFSG.SectionRank.Native
open CFSG.KD.MC.F24C (lay V P N)

@[expose] def selR (lo hi : Nat) (f : CFSG.RankThree.Asc83Table.Native.MFact) : Bool :=
  decide (lo ≤ factMax f ∧ factMax f < hi)

theorem regsA_K : regsV lay V P TT N CoreFi247.nregs (CoreFi247.prog.take 284) RA = true := by
  quickRfl

theorem regsB_K : regsV lay V P TT N CoreFi247.nregs (CoreFi247.prog.take 449) RB = true := by
  quickRfl

theorem regsC_K : regsV lay V P TT N CoreFi247.nregs (CoreFi247.prog.take 575) RC = true := by
  quickRfl

@[expose] noncomputable def chkA (i : Nat) : Bool :=
  chunkV lay V P N RA CoreFi247.nregs CoreFi247.spec.facts HH (selR 0 286) 32 i

@[expose] noncomputable def chkB (i : Nat) : Bool :=
  chunkV lay V P N RB CoreFi247.nregs CoreFi247.spec.facts HH (selR 286 451) 32 i

@[expose] noncomputable def chkC (i : Nat) : Bool :=
  chunkV lay V P N RC CoreFi247.nregs CoreFi247.spec.facts HH (selR 451 577) 32 i

theorem nfacts : CoreFi247.spec.facts.length ≤ 8 * 32 := by decide +kernel

end CertificateChecks.KernelMC.F24C

#kc_each CertificateChecks.KernelMC.F24C.chkA 0 8
#kc_each CertificateChecks.KernelMC.F24C.chkB 0 8
#kc_each CertificateChecks.KernelMC.F24C.chkC 0 8

namespace CertificateChecks.KernelMC.F24C

open CFSG.KC.LocalComp.FactsV CFSG.AGLEmbedding.R3 CFSG.SectionRank.Native
open CFSG.KD.MC.F24C (lay V P N)

theorem neg_regs : Bool.not (regsV lay V P (fun s => TT (s + 1)) N CoreFi247.nregs
    (CoreFi247.prog.take 284) RA) = true := by quickRfl

theorem neg_facts : Bool.not (chunkV lay V P N RC CoreFi247.nregs CoreFi247.spec.facts
    (fun i => HH (i + 1)) (selR 0 577) 32 0) = true := by quickRfl

end CertificateChecks.KernelMC.F24C

end
