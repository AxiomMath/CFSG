module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
meta import CFSG.Sporadic.SuzRecog.LevelTwoCheck
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Data.SuzLevelTwoInputs
public import Mathlib
meta import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.L2XCD

meta def strong : Array (Array Nat) := CFSG.Sporadic.SuzRecog.LevelTwoData.xStrongArrs

meta def base : Array Nat := CFSG.Sporadic.SuzRecog.LevelTwoData.xBase.toArray

@[expose] def deriv : List (List Int) :=
  (CFSG.Sporadic.SuzRecog.LevelTwoData.xWords.extract 2
    CFSG.Sporadic.SuzRecog.LevelTwoData.xWords.size).toList

end CertificateChecks.KernelSpor.L2XCD

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.L2XC 1782 11 8 256
  CertificateChecks.KernelSpor.L2XCD.strong CertificateChecks.KernelSpor.L2XCD.base 2
  CertificateChecks.KernelSpor.L2XCD.deriv

end
