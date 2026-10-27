
module

public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Data.Kernel.Spor.ONNegK
public meta import CFSG.Sporadic.ONOddCore.MinusCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

meta def sigM : Array Nat := CFSG.Sporadic.ONOddCore.sigmaArr

end CertificateChecks.KernelSpor.ON

#kon_table CertificateChecks.KernelSpor.ONN.NEG CertificateChecks.KernelSpor.ON.sigM

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def negS (s : Nat) : Bool :=
  negRange ONV.K ONN.NEG (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

end CertificateChecks.KernelSpor.ON

#kon_slices CertificateChecks.KernelSpor.ON.negS 0 1023

#kon_join CertificateChecks.KernelSpor.ON.negAll CertificateChecks.KernelSpor.ON.negS 1023

end
