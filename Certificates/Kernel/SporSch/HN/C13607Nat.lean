module

public import Certificates.Kernel.SporSch.HN.C13607Data
public import Certificates.Kernel.SporSch.HN.Pt2103
public import CFSG.Certificates.Kernel.SporSch.HNNat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenInputs

public section

namespace CertificateChecks.KernelSporSch.HN13607

open CFSG.KS.HNNat CFSG.KS.TW CertificateChecks.KernelSporSch.HNPt2103
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

@[expose] def fiveWord : List ℤ := [1, 7, 6, -17, 9, 1, 6]

theorem letters_ok : (∀ l ∈ fiveWord, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ elevenWord, l ≠ 0 ∧ l.natAbs ≤ 17) := by
  decide +kernel

theorem codes_ok : CFSG.KD.HN13607.uc = elevenWord.map scode ∧
    CFSG.KD.HN13607.wc = fiveWord.map scode ∧ CFSG.KD.HN13607.FXE = [0, 88, 274750, 366789] := by
  decide +kernel

end CertificateChecks.KernelSporSch.HN13607

end
