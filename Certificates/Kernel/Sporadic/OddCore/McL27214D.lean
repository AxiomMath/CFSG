module

public import Certificates.Kernel.LocalQT.PEnumD
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.McLInvData

namespace CertificateChecks.KernelSpor.M27214

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.McLInv CFSG.Sporadic.McL.Native

meta def idM : Array Nat := idTab 275
meta def gJM : Array (Array Nat) := gensJ (orbitData ())
meta def gIM : Array (Array Nat) := (gensJ (orbitData ())).map (invTab 275)
meta def aM : Array Nat := (gensJ (orbitData ()))[0]!
meta def gTM : Array (Array Nat) := gensT (orbitData ())
meta def gRM : Array (Array Nat) := gensR (orbitData ())

end CertificateChecks.KernelSpor.M27214

public section

set_option maxRecDepth 400000

#kpenum_d CertificateChecks.KernelSpor.MLI 275 9 true CertificateChecks.KernelSpor.M27214.gJM
  CertificateChecks.KernelSpor.M27214.gIM CertificateChecks.KernelSpor.M27214.aM 22275

#kpenum_d CertificateChecks.KernelSpor.MLT 275 9 false CertificateChecks.KernelSpor.M27214.gTM
  CertificateChecks.KernelSpor.M27214.gTM CertificateChecks.KernelSpor.M27214.idM 128

#kpenum_d CertificateChecks.KernelSpor.MLR 275 9 false CertificateChecks.KernelSpor.M27214.gRM
  CertificateChecks.KernelSpor.M27214.gRM CertificateChecks.KernelSpor.M27214.idM 729

end
