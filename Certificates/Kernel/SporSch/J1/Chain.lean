module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Schreier.J1CertData
public meta import CFSG.Sporadic.Schreier.J1CertLit
import CFSG.Certificates.Kernel.Common.Harness
public meta import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J1

meta def strongM : Array (Array Nat) := CFSG.Sporadic.Schreier.j1Chain.strongArrs

meta def baseM : Array Nat := CFSG.Sporadic.Schreier.j1Chain.baseArr

@[expose] def derivs : List (List Int) := CFSG.Sporadic.Schreier.j1Chain.derivations

end CertificateChecks.KernelSporSch.J1

#ks_raworb CertificateChecks.KernelSporSch.J1C 3080 12 64 CertificateChecks.KernelSporSch.J1.strongM
  CertificateChecks.KernelSporSch.J1.baseM 2 CertificateChecks.KernelSporSch.J1.derivs

end
