module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
meta import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Data.SuzModelGroupsInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzMGKD

meta def strong : Array (Array Nat) := CFSG.Sporadic.SuzRecog.ModelGroupsData.c1StrongArrs

meta def base : Array Nat := CFSG.Sporadic.SuzRecog.ModelGroupsData.c1Base.toArray

@[expose] def deriv : List (List Int) :=
  (CFSG.Sporadic.SuzRecog.ModelGroupsData.c1Words.extract 2
    CFSG.Sporadic.SuzRecog.ModelGroupsData.c1Words.size).toList

end CertificateChecks.KernelSpor.SuzMGKD

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.SuzMGK 1782 11 8 256
  CertificateChecks.KernelSpor.SuzMGKD.strong CertificateChecks.KernelSpor.SuzMGKD.base 2
  CertificateChecks.KernelSpor.SuzMGKD.deriv

end
