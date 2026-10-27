module

public import Certificates.Kernel.Sporadic.J3K.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelSpor.J3K.subTree 0 22
#kon_slices CertificateChecks.KernelSpor.J3K.tree0Sl 0 10
#kon_slices CertificateChecks.KernelSpor.J3K.labSl 0 10

end
