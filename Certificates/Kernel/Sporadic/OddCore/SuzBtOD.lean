module

public import Certificates.Kernel.Sporadic.OddCore.BTupOCmd
public import CFSG.Certificates.Kernel.Common.Eval
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.OddCore.BTupOCmd
meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
meta import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtOD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def m1G : Array (Array Nat) := decs m1Decs

meta def nl1G : Array (Array Nat) := decs nl1Decs

meta def w0G : Array Nat := CFSG.Sporadic.SuzRecog.C1Model.w0T

meta def c1B : Array Nat := #[0, 2, 1]

meta def oD := CFSG.KS.BTupRGen.orbcData 1782 11 m1G c1B nl1G w0G
meta def oStep : CFSG.KC.Eval.Step := CFSG.KS.BTupRGen.natStep oD
meta def oC : Array Nat := CFSG.KS.BTupRGen.treeIn oD `C
meta def oPRE : Array Nat := CFSG.KS.BTupRGen.treeIn oD `PRE
meta def oTG : Array Nat := CFSG.KS.BTupRGen.treeIn oD `TG

end CertificateChecks.KernelSpor.SuzBtOD

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSpor SuzBtM1O CertificateChecks.KernelSpor.SuzBtOD.oStep
#kc_nattree CertificateChecks.KernelSpor.SuzBtM1O.C CertificateChecks.KernelSpor.SuzBtOD.oC
#kc_nattree CertificateChecks.KernelSpor.SuzBtM1O.PRE CertificateChecks.KernelSpor.SuzBtOD.oPRE
#kc_nattree CertificateChecks.KernelSpor.SuzBtM1O.TG CertificateChecks.KernelSpor.SuzBtOD.oTG

end
