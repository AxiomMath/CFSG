module

public import Certificates.Kernel.Sporadic.ON.SevenDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

set_option Elab.async false

namespace CertificateChecks.KernelSpor.ON

@[expose] noncomputable def ccF (s : Nat) : Bool := ccOK s

#kc_each_unfold ccF 0 26 as CertificateChecks.KernelSpor.ON.cc

end CertificateChecks.KernelSpor.ON

end
