module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzC1EE

open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native

meta def idR : Array Nat := idTab 1782

meta def ct0G : Array (Array Nat) := ct0Gens

meta def ce3G : Array (Array Nat) := ce3Tabs

meta def cosG : Array (Array Nat) := cosTabs
meta def cosGI : Array (Array Nat) := cosInvs

meta def keys : Array (Array Nat) :=
  ((List.range 48).toArray.map fun a => (List.range 4).toArray.map fun i => cosKey a i).flatten

end CertificateChecks.KernelSpor.SuzC1EE

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.SuzC1EQ 1782 11 false CertificateChecks.KernelSpor.SuzC1EE.ct0G
  CertificateChecks.KernelSpor.SuzC1EE.ct0G CertificateChecks.KernelSpor.SuzC1EE.idR 192

#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EH CertificateChecks.KernelSpor.SuzC1EE.ce3G 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EJ CertificateChecks.KernelSpor.SuzC1EE.cosG 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EJI CertificateChecks.KernelSpor.SuzC1EE.cosGI 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1EY CertificateChecks.KernelSpor.SuzC1EE.keys 11

end
