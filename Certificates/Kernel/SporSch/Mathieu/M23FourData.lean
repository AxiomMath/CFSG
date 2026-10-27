module

public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23FourD

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M23OC

meta def idM : Array Nat := Array.range 23

meta def ids4M : Array (Array Nat) := Array.replicate 4 idM

meta def gM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m23CentWords1.map (evalW 23 #[tAM, tBM])).toArray

end CertificateChecks.KernelSporSch.M23FourD

#kmulh CertificateChecks.KernelSporSch.M23F 23 5 CertificateChecks.KernelSporSch.M23FourD.ids4M
  CertificateChecks.KernelSporSch.M23FourD.gM CertificateChecks.KernelSporSch.M23FourD.idM 3000

end
