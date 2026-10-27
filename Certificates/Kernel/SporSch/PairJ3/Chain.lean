
module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3CheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3Words

meta def strongM : Array (Array Nat) := CFSG.Sporadic.Schreier.j3StrongArrs

meta def baseM : Array Nat := CFSG.Sporadic.Schreier.PairJ3.baseArr

@[expose] def D : List (List Int) :=
  [[-2, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2],
    [-3, -3, 1, -3, -3, -3, 1, 3, 3, 3, 1, 3, 3],
    [-3, -3, 1, -3, 1, -3, -3, 1, 3, 3, 3, 3, 1, 3, 3, 3]]

end CertificateChecks.KernelSporSch.PJ3Words

#ks_chars CertificateChecks.KernelSporSch.PJ3Text CFSG.Sporadic.Schreier.j3StrongHex

#ks_raworb CertificateChecks.KernelSporSch.PJ3 6156 13 64 CertificateChecks.KernelSporSch.PJ3Words.strongM
  CertificateChecks.KernelSporSch.PJ3Words.baseM 2 CertificateChecks.KernelSporSch.PJ3Words.D

end
