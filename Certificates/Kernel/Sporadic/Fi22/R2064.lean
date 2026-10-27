module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.FischerOddCore.Fi22CTIRecords
public meta import CFSG.Sporadic.FischerOddCore.Fi22CTIRecords
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowRecords
public import CFSG.Sporadic.FischerOddCore.Fi22SylowRecords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CtiW

@[expose] def D : List (List Int) :=
  [[-9, 7, 2], [-2, -3, 10, 2], [-5, 11, -10, -5, -3, 9, 5, 6]]

theorem w_eq : CFSG.Sporadic.FischerOddCore.ctiW5 =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 12 D := by decide +kernel

meta def sM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.ctiS5

meta def bM : Array Nat := CFSG.Sporadic.FischerOddCore.ctiB5

end CertificateChecks.KernelSpor.Fi22CtiW

#ks_rawchain CertificateChecks.KernelSpor.Fi22Cti5 512 10 4
  CertificateChecks.KernelSpor.Fi22CtiW.sM CertificateChecks.KernelSpor.Fi22CtiW.bM 9
  CertificateChecks.KernelSpor.Fi22CtiW.D

end
