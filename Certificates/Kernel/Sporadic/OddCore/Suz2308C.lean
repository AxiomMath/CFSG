module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.SuzOddCore.GraphArrays
public meta import CFSG.Sporadic.SuzOddCore.GraphArrays
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.SuzOddCore.Arrays
public import CFSG.Sporadic.SuzOddCore.Arrays
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308M

open CFSG.Sporadic.SuzOddCore

meta def sM : Array (Array Nat) := localStrongArrs
meta def bM : Array Nat := localBaseNat.toArray
@[expose] def dM : List (List Int) := localDerivs.toList.drop 8

end CertificateChecks.KernelSpor.OddCore.S2308M

#ks_rawchain CertificateChecks.KernelSpor.S2308LC 280 9 280
  CertificateChecks.KernelSpor.OddCore.S2308M.sM CertificateChecks.KernelSpor.OddCore.S2308M.bM 8
  CertificateChecks.KernelSpor.OddCore.S2308M.dM

end
