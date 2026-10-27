module

public import Certificates.Kernel.MaxD2.McLR.HeisEnum
public import Certificates.Kernel.MaxD2.McLR.HeisData
public import Certificates.Data.Kernel.MaxD2.Heis
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

@[expose] noncomputable def commsK (lo m : Nat) : Bool :=
  allN m (fun d => allN (Nat.succ (Nat.add lo d)) (fun l =>
    commK 275 9 RE.cnt 5 RE.T (r32 ZP) (r32 CZ) (Nat.add lo d) l))

theorem k_comm0 : commsK 0 56 = true := by quickRfl
theorem k_comm1 : commsK 56 23 = true := by quickRfl
theorem k_comm2 : commsK 79 18 = true := by quickRfl
theorem k_comm3 : commsK 97 15 = true := by quickRfl
theorem k_comm4 : commsK 112 13 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLR

end
