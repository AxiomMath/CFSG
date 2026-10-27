module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
meta import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Data.SuzModelGroupsInputs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzMGJH CFSG.Sporadic.SuzRecog.ModelGroupsData.j0rhoStrongHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzMGJH
  CFSG.Sporadic.SuzRecog.ModelGroupsData.j0rhoStrongHex 3 1782 11 7

namespace CertificateChecks.KernelSpor.SuzMGJD

meta def strong : Array (Array Nat) := CFSG.Sporadic.SuzRecog.ModelGroupsData.j0rhoStrongArrs

meta def base : Array Nat := CFSG.Sporadic.SuzRecog.ModelGroupsData.j0rhoBase.toArray

@[expose] def deriv : List (List Int) :=
  (CFSG.Sporadic.SuzRecog.ModelGroupsData.j0rhoWords.extract 3
    CFSG.Sporadic.SuzRecog.ModelGroupsData.j0rhoWords.size).toList

end CertificateChecks.KernelSpor.SuzMGJD

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.SuzMGJ 1782 11 8 256
  CertificateChecks.KernelSpor.SuzMGJD.strong CertificateChecks.KernelSpor.SuzMGJD.base 3
  CertificateChecks.KernelSpor.SuzMGJD.deriv

end
