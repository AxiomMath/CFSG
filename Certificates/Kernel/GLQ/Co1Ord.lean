module

public import Certificates.Kernel.TcGen.F2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1OrdData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.Co1OrdK

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.EvenSporadicStandard.Induction.Co1Ord
open CertificateChecks.KernelTc

@[expose] noncomputable def checkOrd (prog : List Instr) (A B : Nat) : Bool :=
  forceB (powN (opsF2K 24) 3 B 2) fun B2 =>
    runK (opsF2K 24) prog (initRegsN (opsF2K 24) 11 (A, A) (B, B2)) fun R =>
      (opsF2K 24).eq (powN (opsF2K 24) 17 R[co1OrdOut]!.1 16) (opsF2K 24).one &&
      (opsF2K 24).vne ((opsF2K 24).vmul ((opsF2K 24).unit 0)
        (powN (opsF2K 24) 9 R[co1OrdOut]!.1 8)) ((opsF2K 24).unit 0)

theorem kOrd : checkOrd co1OrdProg C1A.M C1B.M = true := by
  quickRfl

end CertificateChecks.KernelGLQ.Co1OrdK

end
