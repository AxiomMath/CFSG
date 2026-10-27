module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.ON2129
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs
meta import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanParCheckInputs
meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelSpor.ONPar

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar

meta def commG : Array (Array Nat) := onpCommGens

meta def id32 : Array Nat := idTab 32

meta def rG : Array (Array Nat) := onpRGens

meta def rGI : Array (Array Nat) := onpRGensInv

meta def vBar : Array Nat := onpVBar

meta def tInvM : List Nat :=
  (List.range 512).map fun j =>
    (t32Enum.tabs.findIdx? (· == invTab 32 t32Enum.tabs[j]!)).getD 512

meta def PKM : List Nat :=
  [CFSG.KS.RawGen.pack 6 Data.T32z, CFSG.KS.RawGen.pack 6 onpV32,
    CFSG.KS.RawGen.pack 7 Data.quotientConjugator,
    CFSG.KS.RawGen.pack 7 (pinvCand 120 Data.quotientConjugator), CFSG.KS.RawGen.pack 7 onpVB] ++
  ((wordArrs Data.MWords).map fun g => CFSG.KS.RawGen.pack 7 (bTab g)).toList

end CertificateChecks.KernelSpor.ONPar

#kpenum CertificateChecks.KernelSpor.ONPC 32 6 false CertificateChecks.KernelSpor.ONPar.commG
  CertificateChecks.KernelSpor.ONPar.commG CertificateChecks.KernelSpor.ONPar.id32 16

#kpenum CertificateChecks.KernelSpor.ONPO 120 7 true CertificateChecks.KernelSpor.ONPar.rG
  CertificateChecks.KernelSpor.ONPar.rGI CertificateChecks.KernelSpor.ONPar.vBar 400

#knatlist CertificateChecks.KernelSpor.ONPar.tInv CertificateChecks.KernelSpor.ONPar.tInvM

#knatlist CertificateChecks.KernelSpor.ONPar.PK CertificateChecks.KernelSpor.ONPar.PKM

end
