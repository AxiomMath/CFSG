module

public import Certificates.Data.SuzOutComp
public import Certificates.Data.Kernel.Misc.SuzOut
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.SuzOutComp

set_option maxRecDepth 400000
#ks_chars CertificateChecks.KernelSuzOut.T3AbC CFSG.ComponentClassification.SuzOutComp.Native.t3AbText
#ks_chars CertificateChecks.KernelSuzOut.T3XwC
  CFSG.ComponentClassification.SuzOutComp.Native.t3XWordsText
#ks_chars CertificateChecks.KernelSuzOut.T3DwC
  CFSG.ComponentClassification.SuzOutComp.Native.t3DWordsText
#ks_chars CertificateChecks.KernelSuzOut.T3LabelsC
  CFSG.ComponentClassification.SuzOutComp.Native.t3LabelsText
#ks_chars CertificateChecks.KernelSuzOut.T3RootsC
  CFSG.ComponentClassification.SuzOutComp.Native.t3RootsText
#ks_chars CertificateChecks.KernelSuzOut.T3TwC CFSG.ComponentClassification.SuzOutComp.Native.t3TwText
#ks_chars CertificateChecks.KernelSuzOut.T3HwC CFSG.ComponentClassification.SuzOutComp.Native.t3HwText
#ks_chars CertificateChecks.KernelSuzOut.T3ReC
  CFSG.ComponentClassification.SuzOutComp.Native.t3ReachText

public section

namespace CertificateChecks.KernelSuzOut

@[expose] noncomputable def derivX3 : List (List Int) := CFSG.KC.SuzOut.wordsK T3XwC.chars

@[expose] noncomputable def derivD3 : List (List Int) := CFSG.KC.SuzOut.wordsK T3DwC.chars

end CertificateChecks.KernelSuzOut

end

namespace CertificateChecks.KernelSuzOut.T3M

open CFSG.ComponentClassification.SuzOutComp.Native CFSG.Sporadic.SuzOddCore

meta def fix : Array (Array Nat) := #[(fixList 3).toArray]

meta def labels : Array (Array Nat) := #[t3Labels]

meta def roots : Array (Array Nat) := #[t3Roots]

meta def strongX : Array (Array Nat) := t3XStrong

meta def strongD : Array (Array Nat) := t3DStrong

meta def base : Array Nat := #[0, 1, 2, 3]

end CertificateChecks.KernelSuzOut.T3M

#kmisc_packarrs CertificateChecks.KernelSuzOut.T3Fx CertificateChecks.KernelSuzOut.T3M.fix 11
#kmisc_packarrs CertificateChecks.KernelSuzOut.T3Lc CertificateChecks.KernelSuzOut.T3M.labels 2
#kmisc_packarrs CertificateChecks.KernelSuzOut.T3Rc CertificateChecks.KernelSuzOut.T3M.roots 7

#ks_rawchain CertificateChecks.KernelSuzOut.T3X 100 7 50 CertificateChecks.KernelSuzOut.T3M.strongX
  CertificateChecks.KernelSuzOut.T3M.base 5 CertificateChecks.KernelSuzOut.derivX3

#ks_rawchain CertificateChecks.KernelSuzOut.T3D 100 7 50 CertificateChecks.KernelSuzOut.T3M.strongD
  CertificateChecks.KernelSuzOut.T3M.base 2 CertificateChecks.KernelSuzOut.derivD3
