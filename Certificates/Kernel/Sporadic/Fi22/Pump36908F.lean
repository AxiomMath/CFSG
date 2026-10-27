module

public import Certificates.Kernel.Sporadic.Fi22.Five8124K
public import Certificates.Data.Kernel.Fi22Pump.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Pump36908

open CFSG.KC.Enum CFSG.KS CFSG.KC.Fi22Pump
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fv8124 (ev idP Q1 Q2)

@[expose] noncomputable def rowsF (q : Nat) : Bool :=
  allN 60 fun i => strictB (Fv8124E.T i) fun t =>
    rowF (ev t) (ev q) CFSG.RankThree.Native.fi22FiveKeyPts (Nat.beq t idP)

theorem okF : strictB Q2 rowsF = true := by quickRfl

end CertificateChecks.KernelSpor.Pump36908

end
