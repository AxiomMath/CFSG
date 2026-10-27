
module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

meta def t3S : Array (Array Nat) := extendArrs aArrs witRec.third.strongDerivations

meta def t3B : Array Nat := witRec.third.baseIndices.toArray

@[expose] def t3D : List (List Int) := witRec.third.strongDerivations

end CertificateChecks.KernelSporSch.Co2M

#ks_raworb CertificateChecks.KernelSporSch.Co2T3 2300 12 256
  CertificateChecks.KernelSporSch.Co2M.t3S CertificateChecks.KernelSporSch.Co2M.t3B 2
  CertificateChecks.KernelSporSch.Co2M.t3D

end
