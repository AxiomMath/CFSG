module

public import Certificates.Data.Kernel.Ivk8NormPK
public import Certificates.Kernel.Ivk8J2.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KS.Ivk8NormP.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Ivk8Cent CFSG.KS.Ivk8NormP CertificateChecks.KernelIvk8J2
  CertificateChecks.KernelSpor

@[expose] def prs (hs : List Nat) : List (Nat × Nat) := hs.map fun h => (h, h)

@[expose] noncomputable def chk5 (p : Nat) (c ci : List Nat) (cnt : Nat) (T : Nat → Nat) : Bool :=
  wH fun _ _ _ hs => strictB (evW 315 9 lt c) fun x => strictB (evW 315 9 lt ci) fun xi =>
    chkPK 315 9 p x xi cnt T (prs hs)

theorem ch5253_j2_q2a1 : chk5 5 c1 c1i J2Q2a.cnt J2Q2a.T = true := by quickRfl

theorem ch5253_j2_q2b1 : chk5 5 c1 c1i J2Q2b.cnt J2Q2b.T = true := by quickRfl

theorem ch5253_j2_q2a3 : chk5 5 c3 c3i J2Q2a.cnt J2Q2a.T = true := by quickRfl

theorem ch5253_j2_q2b3 : chk5 5 c3 c3i J2Q2b.cnt J2Q2b.T = true := by quickRfl

theorem ch5253_j2_q3b : chk5 5 c2 c2i J2Q3b.cnt J2Q3b.T = true := by quickRfl

theorem ch5253_j2_q3c : chk5 5 c2 c2i J2Q3c.cnt J2Q3c.T = true := by quickRfl

end CFSG.KS.Ivk8NormP.J2

end
