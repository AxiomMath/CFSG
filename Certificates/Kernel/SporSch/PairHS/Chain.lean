module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHSWords

meta def strongM : Array (Array Nat) := CFSG.Sporadic.Schreier.hsStrongArrs

meta def baseM : Array Nat := CFSG.Sporadic.Schreier.PairHS.baseArr

@[expose] def D : List (List Int) :=
  [[-2, 1, -2, 1, 2, 1, 2],
    [-2, 1, -2, -2, -2, -2, 1, 2, 2, 2, 2, 1, 2],
    [4, 3, 4],
    [1, -2, -2, 1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1],
    [3, 6, 3],
    [1, -2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, 2, 2]]

end CertificateChecks.KernelSporSch.PHSWords

#ks_raworb CertificateChecks.KernelSporSch.PHSC 3850 12 64 CertificateChecks.KernelSporSch.PHSWords.strongM
  CertificateChecks.KernelSporSch.PHSWords.baseM 2 CertificateChecks.KernelSporSch.PHSWords.D

end
