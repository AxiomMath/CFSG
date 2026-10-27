module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
public import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtND

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def cl1G : Array (Array Nat) := decs cl1Decs

meta def m1G : Array (Array Nat) := decs m1Decs

meta def c1B : Array Nat := #[0, 2, 1]

meta def zD := CFSG.KS.BTupRGen.ruData 1782 11 cl1G c1B cl1G m1G
meta def zS : Array Nat := CFSG.KS.BTupRGen.treeIn zD `S
meta def zT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `T
meta def zRT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `RT
meta def zIX : Array Nat := CFSG.KS.BTupRGen.treeIn zD `IX

end CertificateChecks.KernelSpor.SuzBtND

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtCL1 1782 11 CertificateChecks.KernelSpor.SuzBtND.cl1G
  CertificateChecks.KernelSpor.SuzBtND.c1B

#kc_nattree CertificateChecks.KernelSpor.SuzBtCL1Z.S CertificateChecks.KernelSpor.SuzBtND.zS
#kc_nattree CertificateChecks.KernelSpor.SuzBtCL1Z.T CertificateChecks.KernelSpor.SuzBtND.zT
#kc_nattree CertificateChecks.KernelSpor.SuzBtCL1Z.RT CertificateChecks.KernelSpor.SuzBtND.zRT
#kc_nattree CertificateChecks.KernelSpor.SuzBtCL1Z.IX CertificateChecks.KernelSpor.SuzBtND.zIX

end
