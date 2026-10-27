module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
public import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtZD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def m1G : Array (Array Nat) := decs m1Decs

meta def l1G : Array (Array Nat) := decs l1Decs

meta def c1B : Array Nat := #[0, 2, 1]

meta def zD := CFSG.KS.BTupRGen.ruData 1782 11 m1G c1B m1G l1G
meta def zS : Array Nat := CFSG.KS.BTupRGen.treeIn zD `S
meta def zT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `T
meta def zRT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `RT
meta def zIX : Array Nat := CFSG.KS.BTupRGen.treeIn zD `IX

end CertificateChecks.KernelSpor.SuzBtZD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtL1 1782 11 CertificateChecks.KernelSpor.SuzBtZD.l1G
  CertificateChecks.KernelSpor.SuzBtZD.c1B

#kc_nattree CertificateChecks.KernelSpor.SuzBtM1Z.S CertificateChecks.KernelSpor.SuzBtZD.zS
#kc_nattree CertificateChecks.KernelSpor.SuzBtM1Z.T CertificateChecks.KernelSpor.SuzBtZD.zT
#kc_nattree CertificateChecks.KernelSpor.SuzBtM1Z.RT CertificateChecks.KernelSpor.SuzBtZD.zRT
#kc_nattree CertificateChecks.KernelSpor.SuzBtM1Z.IX CertificateChecks.KernelSpor.SuzBtZD.zIX

end
