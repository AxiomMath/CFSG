module

public import Certificates.Kernel.Sporadic.J3C.Checks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3C

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.CentReg

@[expose] noncomputable def sqTest (k : Nat) : Bool :=
  Nat.beq (hd (walkK SL TS.PAR TS.LAB k (List.cons (r32 TS.PTS k) List.nil))) 0

theorem sqOne_ok : Nat.beq (cntN TS.cnt sqTest) 36 = true := by quickRfl

end CertificateChecks.KernelSpor.J3C

end
