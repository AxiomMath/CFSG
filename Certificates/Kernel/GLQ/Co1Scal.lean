module

public import Certificates.Kernel.TcGen.F2
public import CFSG.RankThree.PartOne.KS.Co1ScalInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.Co1ScalK

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.RankThree.PartOne.KS.ScalFive
open CFSG.RankThree.PartOne.KS.Co1Scal CertificateChecks.KernelTc

@[expose] noncomputable def checkCo15 (prog : List Instr) (A B : Nat) : Bool :=
  (opsF2K 24).eq (powN (opsF2K 24) 3 A 2) (opsF2K 24).one &&
    (opsF2K 24).eq (powN (opsF2K 24) 4 B 3) (opsF2K 24).one &&
    forceB (powN (opsF2K 24) 3 B 2) fun B2 =>
      runK (opsF2K 24) prog (initRegsN (opsF2K 24) co1Data.nreg (A, A) (B, B2)) fun R =>
        relsOK (opsF2K 24) co1Data R

theorem kCo15 : checkCo15 co1Prog C1A.M C1B.M = true := by
  quickRfl

end CertificateChecks.KernelGLQ.Co1ScalK

end
