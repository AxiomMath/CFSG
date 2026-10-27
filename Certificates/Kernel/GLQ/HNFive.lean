module

public import Certificates.Kernel.GLQ.HNTwo
public import CFSG.RankThree.PartOne.KS.HNFiveInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.HNFiveK

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.RankThree.PartOne.KS.HNFive
open CertificateChecks.KernelGLQ.HNTwo

@[expose] noncomputable def checkHN5 (prog : List Instr) (A B : Nat) : Bool :=
  vld A && vld B && forceB (powN O5 3 B 2) fun B2 =>
    runK O5 prog (initRegsN O5 hnFiveN (A, A) (B, B2)) fun R => relsOK O5 R

theorem kHN5 : forceB (pay HS1.chars) (fun A => forceB (pay HS2.chars) fun B =>
    checkHN5 hnFiveProg A B) = true := by
  quickRfl

end CertificateChecks.KernelGLQ.HNFiveK

end
