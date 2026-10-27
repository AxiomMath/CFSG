module

public import Certificates.Data.SuzOutComp
public import Certificates.Data.Kernel.Misc.SuzOut
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.SuzOutComp

set_option maxRecDepth 400000
#ks_chars CertificateChecks.KernelSuzOut.T2LabC CFSG.ComponentClassification.SuzOutComp.Native.t2LabText
#ks_chars CertificateChecks.KernelSuzOut.T2RepC CFSG.ComponentClassification.SuzOutComp.Native.t2RepText
#ks_chars CertificateChecks.KernelSuzOut.T2AbC CFSG.ComponentClassification.SuzOutComp.Native.t2AbText
#ks_chars CertificateChecks.KernelSuzOut.T2XwC
  CFSG.ComponentClassification.SuzOutComp.Native.t2XWordsText
#ks_chars CertificateChecks.KernelSuzOut.T2DwC
  CFSG.ComponentClassification.SuzOutComp.Native.t2DWordsText
#ks_chars CertificateChecks.KernelSuzOut.T2LabelsC
  CFSG.ComponentClassification.SuzOutComp.Native.t2LabelsText
#ks_chars CertificateChecks.KernelSuzOut.T2RootsC
  CFSG.ComponentClassification.SuzOutComp.Native.t2RootsText
#ks_chars CertificateChecks.KernelSuzOut.T2TwC CFSG.ComponentClassification.SuzOutComp.Native.t2TwText
#ks_chars CertificateChecks.KernelSuzOut.T2HwC CFSG.ComponentClassification.SuzOutComp.Native.t2HwText
#ks_chars CertificateChecks.KernelSuzOut.T2ReC
  CFSG.ComponentClassification.SuzOutComp.Native.t2ReachText

namespace CertificateChecks.KernelSuzOut.T2M

open CFSG.ComponentClassification.SuzOutComp.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

meta def lab : Array (Array Nat) := #[t2Lab]

meta def rep : Array (Array Nat) := #[t2Rep]

meta def labels : Array (Array Nat) := #[t2Labels]

meta def roots : Array (Array Nat) := #[t2Roots]

meta def rows : Array (Array Nat) :=
  let S := t2DStrong
  let delta := (List.range 396).filter fun p => t2Labels[p]! == t2Labels[1]!
  (Array.range 396).map fun x =>
    let c := wordA 396 S (rawInvs 396 S) t2Tw[x]!
    (delta.map fun y => c.getD y 0).toArray

end CertificateChecks.KernelSuzOut.T2M

#kmisc_packarrs CertificateChecks.KernelSuzOut.T2Lb CertificateChecks.KernelSuzOut.T2M.lab 9
#kmisc_packarrs CertificateChecks.KernelSuzOut.T2Rp CertificateChecks.KernelSuzOut.T2M.rep 11
#kmisc_packarrs CertificateChecks.KernelSuzOut.T2Lc CertificateChecks.KernelSuzOut.T2M.labels 4
#kmisc_packarrs CertificateChecks.KernelSuzOut.T2Rc CertificateChecks.KernelSuzOut.T2M.roots 9
#kmisc_packarrs CertificateChecks.KernelSuzOut.T2Rw CertificateChecks.KernelSuzOut.T2M.rows 9
