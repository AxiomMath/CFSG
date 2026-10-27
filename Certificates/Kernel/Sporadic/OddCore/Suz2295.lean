module

public import Certificates.Kernel.Sporadic.OddCore.Suz2289
public import Certificates.Kernel.Sporadic.OddCore.SuzOuter
public import Certificates.Kernel.Sporadic.OddCore.SuzCenter
public import Certificates.Kernel.Sporadic.OddCore.SuzLocal
public import CFSG.Certificates.Kernel.Spor.MatKSound
public import CFSG.Sporadic.SuzOddCore.GraphArraysCheckInputs
import all CFSG.Sporadic.SuzOddCore.GraphArrays
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzMatT CFSG.Sporadic.SuzOddCore.suzd2F3r64aM1Text

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Row
open CFSG.Certificates.Native

theorem mat_ok : CFSG.KC.MatK.matK SuzMatT.chars 1 3 64 64 4096 = true := by
  quickRfl

theorem words2295 : derivsOK 8 localDerivs = true ∧ localDerivs.size = 14 ∧
    lettersOK 10 zWord = true ∧ (∀ w ∈ sylowQuotWords, lettersOK 14 w = true) ∧
    (∀ w ∈ normalizingSiftWords, ∀ v ∈ w, lettersOK 10 v = true) ∧
    (∀ w ∈ normWords, lettersOK 8 w = true) := by
  decide +kernel

theorem facts2295 :
    permOK 22880 outerArr = true ∧ (∀ k < 22, permOK 280 (localRun k) = true) ∧
    (∀ r < 9, permOK 22880 (centerFull r) = true ∧ permOK 280 (centerCompact r) = true) ∧
    localDomain.length = 280 ∧ strictIncr localDomain = true ∧ (∀ x ∈ localDomain, x < 22880) ∧
    derivsOK 8 localDerivs = true ∧ localDerivs.size = 14 ∧ lettersOK 10 zWord = true ∧
    (∀ w ∈ sylowQuotWords, lettersOK 14 w = true) ∧
    (∀ w ∈ normalizingSiftWords, ∀ v ∈ w, lettersOK 10 v = true) ∧
    (∀ w ∈ normWords, lettersOK 8 w = true) ∧
    matHeader suzd2F3r64aM1Text = [1, 3, 64, 64] ∧ (matDigits suzd2F3r64aM1Text).length = 4096 ∧
    (∀ c ∈ matDigits suzd2F3r64aM1Text, c = '0' ∨ c = '1' ∨ c = '2') := by
  have hm := CFSG.KC.MatK.matK_sound mat_ok
  rw [← SuzMatT.eq] at hm
  obtain ⟨d1, d2, d3⟩ := domain
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := words2295
  refine ⟨?_, fun k hk => ?_, fun r hr => ⟨?_, ?_⟩, d1, d2, d3, w1, w2, w3, w4, w5, w6, hm.1,
    hm.2.1, hm.2.2⟩
  · rw [outerArr_eq]
    exact permOK_rows outer_perm
  · rw [localRun_eq hk]
    exact permOK_unpack (allN_spec run_perms k hk)
  · rw [centerFull_eq hr]
    exact permOK_rows (allN_spec full_perms r hr)
  · rw [centerCompact_eq hr]
    exact permOK_unpack (allN_spec comp_perms r hr)

end CertificateChecks.KernelSpor.OddCore

end
