module

public import Certificates.Data.Kernel.EvenSporG24Hex.Defs
public meta import Certificates.Kernel.EvenSporG24Hex.Gen
public import CFSG.Certificates.Kernel.Common.Eval

public section

#kc_eval CertificateChecks.KernelG24Hex D CertificateChecks.KernelG24Hex.stepG24Hex

namespace CertificateChecks.KernelG24Hex

open CFSG.KC.EvenSporG24Hex

@[expose] noncomputable def hexF (j : Nat) : Bool := hexJ D.U D.W D.GE D.PG D.LC j

end CertificateChecks.KernelG24Hex

end
