module

public import Certificates.Kernel.MaxD2.McLR.Enum
public import Certificates.Kernel.MaxD2.McLR.Data
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

@[expose] noncomputable def repsK (q : Nat) : Bool :=
  allN 17 (fun d => repK 275 9 2 18 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add (Nat.add 1 (Nat.mul 17 q)) d))

theorem rep_t0 : repsK 0 = true := by quickRfl
theorem rep_t1 : repsK 1 = true := by quickRfl
theorem rep_t2 : repsK 2 = true := by quickRfl
theorem rep_t3 : repsK 3 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLR

end
