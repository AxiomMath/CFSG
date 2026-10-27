module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.TextBlocks
public import Certificates.Kernel.Misc.RuFourth.Data
public import CFSG.Sporadic.Recognition.RuMultiplierData
public import Certificates.Data.CFSGNative.Bridge.SurjD
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.TextAtSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.RuFRT CFSG.Sporadic.Recognition.RuMultiplier.ruRhoText

#ks_chars CertificateChecks.KernelMisc.RuFST CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText

namespace CertificateChecks.KernelMisc.RuFourth

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KC.Misc.RuFourth
  CertificateChecks.KernelMisc.TextBlocks

@[expose] noncomputable def lineOK (k : Nat) : Bool :=
  lineK 4 16240 14 (RK k) (RuFRT.chars.drop (64960 * k))

theorem line0 : lineOK 0 = true := by quickRfl
theorem line1 : lineOK 1 = true := by quickRfl
theorem line2 : lineOK 2 = true := by quickRfl

theorem asciiB : asciiBlocks 12 16240 RuFRT.chars = true := by
  quickRfl

theorem textS : wordsTextOK RuFST.chars = true := by
  quickRfl

theorem textS_neg : (!wordsTextOK ['1', ' ', ' ', '2'] && !wordsTextOK ['-', '-', '2'] &&
    !wordsTextOK ['-', '0']) = true := by
  decide +kernel

theorem intsK_minus_zero : intsK ['-', '0'] = [-1] := by
  decide +kernel

end CertificateChecks.KernelMisc.RuFourth

end
