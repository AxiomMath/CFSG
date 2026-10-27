module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
public import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtSZD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def s1G : Array (Array Nat) := decs s1pDecs

meta def m1G : Array (Array Nat) := decs m1Decs

meta def l1G : Array (Array Nat) := decs l1Decs

meta def t1G : Array (Array Nat) := #[CFSG.ComponentClassification.AS81.SuzB0.tTab]

meta def c1B : Array Nat := #[0, 2, 1]

meta def zD := CFSG.KS.BTupRGen.ruData 1782 11 s1G c1B s1G t1G
meta def zS : Array Nat := CFSG.KS.BTupRGen.treeIn zD `S
meta def zT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `T
meta def zRT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `RT
meta def zIX : Array Nat := CFSG.KS.BTupRGen.treeIn zD `IX

meta def lD := CFSG.KS.BTupRGen.ruData 1782 11 s1G c1B l1G m1G
meta def lS : Array Nat := CFSG.KS.BTupRGen.treeIn lD `S
meta def lT : Array Nat := CFSG.KS.BTupRGen.treeIn lD `T
meta def lRT : Array Nat := CFSG.KS.BTupRGen.treeIn lD `RT
meta def lIX : Array Nat := CFSG.KS.BTupRGen.treeIn lD `IX

end CertificateChecks.KernelSpor.SuzBtSZD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtT1 1782 11 CertificateChecks.KernelSpor.SuzBtSZD.t1G
  CertificateChecks.KernelSpor.SuzBtSZD.c1B

#kc_nattree CertificateChecks.KernelSpor.SuzBtS1Z.S CertificateChecks.KernelSpor.SuzBtSZD.zS
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1Z.T CertificateChecks.KernelSpor.SuzBtSZD.zT
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1Z.RT CertificateChecks.KernelSpor.SuzBtSZD.zRT
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1Z.IX CertificateChecks.KernelSpor.SuzBtSZD.zIX

#kc_nattree CertificateChecks.KernelSpor.SuzBtS1L.S CertificateChecks.KernelSpor.SuzBtSZD.lS
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1L.T CertificateChecks.KernelSpor.SuzBtSZD.lT
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1L.RT CertificateChecks.KernelSpor.SuzBtSZD.lRT
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1L.IX CertificateChecks.KernelSpor.SuzBtSZD.lIX

end
