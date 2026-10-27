module

public import Certificates.Kernel.Sporadic.OddCore.BTupCmd
public import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtTD

meta def t0G : Array (Array Nat) := CFSG.Sporadic.SuzRecog.C1Model.t0Tabs

meta def c1B : Array Nat := #[0, 2, 1]

meta def zD := CFSG.KS.BTupRGen.ruData 1782 11 t0G c1B t0G t0G
meta def zS : Array Nat := CFSG.KS.BTupRGen.treeIn zD `S
meta def zT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `T
meta def zRT : Array Nat := CFSG.KS.BTupRGen.treeIn zD `RT
meta def zIX : Array Nat := CFSG.KS.BTupRGen.treeIn zD `IX

end CertificateChecks.KernelSpor.SuzBtTD

public section

set_option maxRecDepth 400000

#kbtup CertificateChecks.KernelSpor.SuzBtT0 1782 11 CertificateChecks.KernelSpor.SuzBtTD.t0G
  CertificateChecks.KernelSpor.SuzBtTD.c1B

#kc_nattree CertificateChecks.KernelSpor.SuzBtT0Z.S CertificateChecks.KernelSpor.SuzBtTD.zS
#kc_nattree CertificateChecks.KernelSpor.SuzBtT0Z.T CertificateChecks.KernelSpor.SuzBtTD.zT
#kc_nattree CertificateChecks.KernelSpor.SuzBtT0Z.RT CertificateChecks.KernelSpor.SuzBtTD.zRT
#kc_nattree CertificateChecks.KernelSpor.SuzBtT0Z.IX CertificateChecks.KernelSpor.SuzBtTD.zIX

end
