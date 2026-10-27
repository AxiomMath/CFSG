module

public import Certificates.Kernel.MatCert.Ly
public import CFSG.RankThree.PartOne.KS.LyScalInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.LyScalK

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.RankThree.PartOne.KS.ScalFive
open CFSG.RankThree.PartOne.KS.LyScal CertificateChecks.KernelMC CertificateChecks.KernelSporSch

@[expose] noncomputable def checkLy5 (prog : List Instr) (A B : Nat) : Bool :=
  forceB (powN OL 5 B 4) fun B4 =>
    runK OL prog (initRegsN OL lyData.nreg (A, A) (B, B4)) fun R => relsOK OL lyData R

theorem kLy5 : checkLy5 lyProg LyBS.A LyBS.B = true := by
  quickRfl

end CertificateChecks.KernelGLQ.LyScalK

end
