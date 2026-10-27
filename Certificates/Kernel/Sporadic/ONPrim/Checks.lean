module

public import Certificates.Kernel.Sporadic.ONNQ.Tabs
public import Certificates.Kernel.Sporadic.ONPrim.Data
public import Certificates.Data.Kernel.Spor.ONPrimK

public section

namespace CertificateChecks.KernelSpor.ONPrim

open CFSG.KS.ONPrim CertificateChecks.KernelSpor.ONNQ

@[expose] noncomputable def prBlS (s : Nat) : Bool :=
  primBlk TT UU ONPr.R ONPr.C (nat_lit 122760) (nat_lit 1240) s

@[expose] noncomputable def prTot : Bool := primTot ONPr.C (nat_lit 99)

@[expose] noncomputable def prHead : Bool := primHead TT

end CertificateChecks.KernelSpor.ONPrim

end
