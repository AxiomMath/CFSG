module

public import Certificates.Kernel.Sporadic.OddCore.J2Loc
public import Certificates.Kernel.GH74.J2X
public import Certificates.Data.Kernel.GH74Ev
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2Cent5

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.GH74

@[expose] noncomputable def slice (s : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 64) s) (fun k => cent5At 315 9 KernelSpor.J2C2.cnt KernelSpor.J2C2.T
    (KernelSpor.J2CentT.F 31) (KernelGH74.J2XT 2) (KernelSpor.J2C2.T k)) (nat_lit 64)

end CertificateChecks.KernelGH74.J2Cent5

#kon_slices CertificateChecks.KernelGH74.J2Cent5.slice 0 30
#kon_join CertificateChecks.KernelGH74.J2Cent5.all CertificateChecks.KernelGH74.J2Cent5.slice 30

end
