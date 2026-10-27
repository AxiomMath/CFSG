module

public import Certificates.Kernel.Sporadic.OddCore.BTupCCmd
public import CFSG.Certificates.Kernel.Common.Eval
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.Sporadic.OddCore.BTupCCmd
meta import Certificates.Kernel.Sporadic.OddCore.BTupRCmd
meta import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzBtCD

open CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def s1G : Array (Array Nat) := decs s1pDecs

meta def l1G : Array (Array Nat) := decs l1Decs

meta def c1B : Array Nat := #[0, 2, 1]

meta def cD := CFSG.KS.BTupRGen.clsData 1782 11 s1G c1B l1G
meta def cStep : CFSG.KC.Eval.Step := CFSG.KS.BTupRGen.natStep cD
meta def cTG : Array Nat := CFSG.KS.BTupRGen.treeIn cD `TG
meta def cE : Array Nat := CFSG.KS.BTupRGen.treeIn cD `E

end CertificateChecks.KernelSpor.SuzBtCD

public section

set_option maxRecDepth 400000

#kc_eval CertificateChecks.KernelSpor SuzBtS1C CertificateChecks.KernelSpor.SuzBtCD.cStep
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1C.TG CertificateChecks.KernelSpor.SuzBtCD.cTG
#kc_nattree CertificateChecks.KernelSpor.SuzBtS1C.E CertificateChecks.KernelSpor.SuzBtCD.cE

end
