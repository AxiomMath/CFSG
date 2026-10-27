module

public import Certificates.Data.Kernel.Misc.TitsOuter
public import CFSG.Certificates.Kernel.YModel.TextGenS
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Tits.Pi7092
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
meta import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.Kernel.Misc.TitsAbText
meta import Certificates.Data.Kernel.Misc.TitsAbText

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.TitsAbC CFSG.Quasithin.titsAbWordsText
#ym_texts CertificateChecks.KernelMisc.TitsAbT CertificateChecks.KernelMisc.titsAbChainText 32 1
#ym_texts CertificateChecks.KernelMisc.TitsLbT CFSG.Quasithin.titsLabelsText 32 1

public section

namespace CertificateChecks.KernelMisc.TitsOut

open CFSG.KC.Enum CFSG.KC.YModel CFSG.KC.TitsOuter CFSG.KS CertificateChecks.KernelSpor.Tits2264

theorem abChars : charsOf TitsAbT.CH = '0' :: TitsAbC.chars := by decide +kernel

@[expose] def labA : List Nat := [0, 1, 6, 24, 87]

@[expose] def labB : List Nat := [0, 2, 8, 30, 110]

theorem lab : labOK 1755 (TitsLbT.F 0) labA labB = true := by decide +kernel

@[expose] noncomputable def cj (j : Nat) : Nat :=
  pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) TitsPi.P (KernelSpor.TitsD.S j))
    (pinvS 1755 11 (mask 11) TitsPi.P)

theorem conj : allN 2 (fun j => bAnd(siftD (cj j), permC (cj j))) = true := by decide +kernel

end CertificateChecks.KernelMisc.TitsOut

end
