module

public import Certificates.Kernel.Sporadic.McLC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

@[expose] noncomputable def alOK : Bool :=
  allN (nat_lit 275) fun x =>
    Nat.beq (r32 McLK.AL x) (List.foldr GK x [nat_lit 1, 1, 1, 1, 1, 1, 1])

theorem alOK_ok : alOK = true := by quickRfl

end CertificateChecks.KernelSpor.McLC

end
