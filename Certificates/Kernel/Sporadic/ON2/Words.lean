module

public import Certificates.Kernel.Sporadic.ON2.GenWords
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.WordsTxtSound
public meta import Certificates.Data.CFSGNative.Bridge.ONGPL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.ONGI CFSG.Sporadic.Bridge.ONGPL.Native.imgText

#ks_chars CertificateChecks.KernelSpor.ONGS CFSG.Sporadic.Bridge.ONGPL.Native.surjText

namespace CertificateChecks.KernelSpor.ON2

open CFSG.Sporadic.Bridge.ONGPL.Native

meta def imgM : Array (List Int) := imgWords ()

meta def surjM : Array (List Int) := surjWords ()

meta def relsM : Array (List Int) := ((rels ()).map fun r => r.map letterOf).toArray

end CertificateChecks.KernelSpor.ON2

#kon_words CertificateChecks.KernelSpor.IMW CertificateChecks.KernelSpor.ON2.imgM

#kon_words CertificateChecks.KernelSpor.SRW CertificateChecks.KernelSpor.ON2.surjM

#kon_words CertificateChecks.KernelSpor.RLW CertificateChecks.KernelSpor.ON2.relsM

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KS.Words

theorem imgOK : wordsK ONGI.chars IMW.WC IMW.WL 7 = true := by quickRfl

theorem surjOK : wordsK ONGS.chars SRW.WC SRW.WL 2 = true := by quickRfl

end CertificateChecks.KernelSpor.ON2

end
