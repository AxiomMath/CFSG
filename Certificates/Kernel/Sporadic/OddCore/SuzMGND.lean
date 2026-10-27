module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
meta import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Data.SuzModelGroupsInputs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzMGNH CFSG.Sporadic.SuzRecog.ModelGroupsData.nr0StrongHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzMGNH
  CFSG.Sporadic.SuzRecog.ModelGroupsData.nr0StrongHex 3 1782 11 9

namespace CertificateChecks.KernelSpor.SuzMGND

meta def strong : Array (Array Nat) := CFSG.Sporadic.SuzRecog.ModelGroupsData.nr0StrongArrs

meta def base : Array Nat := CFSG.Sporadic.SuzRecog.ModelGroupsData.nr0Base.toArray

@[expose] def deriv : List (List Int) :=
  (CFSG.Sporadic.SuzRecog.ModelGroupsData.nr0Words.extract 5
    CFSG.Sporadic.SuzRecog.ModelGroupsData.nr0Words.size).toList

end CertificateChecks.KernelSpor.SuzMGND

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.SuzMGN 1782 11 8 256
  CertificateChecks.KernelSpor.SuzMGND.strong CertificateChecks.KernelSpor.SuzMGND.base 5
  CertificateChecks.KernelSpor.SuzMGND.deriv

end
