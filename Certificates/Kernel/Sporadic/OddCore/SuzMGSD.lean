module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
meta import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Data.SuzModelGroupsInputs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzMGSH
  CFSG.Sporadic.SuzRecog.ModelGroupsData.csplitStrongHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzMGSH
  CFSG.Sporadic.SuzRecog.ModelGroupsData.csplitStrongHex 3 1782 11 9

namespace CertificateChecks.KernelSpor.SuzMGSD

meta def strong : Array (Array Nat) := CFSG.Sporadic.SuzRecog.ModelGroupsData.csplitStrongArrs

meta def base : Array Nat := CFSG.Sporadic.SuzRecog.ModelGroupsData.csplitBase.toArray

@[expose] def deriv : List (List Int) :=
  (CFSG.Sporadic.SuzRecog.ModelGroupsData.csplitWords.extract 4
    CFSG.Sporadic.SuzRecog.ModelGroupsData.csplitWords.size).toList

end CertificateChecks.KernelSpor.SuzMGSD

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.SuzMGS 1782 11 8 256
  CertificateChecks.KernelSpor.SuzMGSD.strong CertificateChecks.KernelSpor.SuzMGSD.base 4
  CertificateChecks.KernelSpor.SuzMGSD.deriv

end
