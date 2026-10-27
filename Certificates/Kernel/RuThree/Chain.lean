module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

meta def baseM : Array Nat := CFSG.EvenSporadicStandard.RuStd.S2.ruThreeBaseArr

@[expose] def derivs : List (List Int) := CFSG.EvenSporadicStandard.RuStd.S2.ruThreeWords.toList.drop 2

end CertificateChecks.KernelRuThree

#ks_chars CertificateChecks.KernelRuThree.R3A CFSG.EvenSporadicStandard.RuStd.S2.ruThreeHexA
#ks_chars CertificateChecks.KernelRuThree.R3B CFSG.EvenSporadicStandard.RuStd.S2.ruThreeHexB
#ks_chars CertificateChecks.KernelRuThree.R3C CFSG.EvenSporadicStandard.RuStd.S2.ruThreeHexC

namespace CertificateChecks.KernelRuThree.R3

@[expose] noncomputable def chars : List Char := R3A.chars ++ (R3B.chars ++ R3C.chars)

theorem eq : CFSG.EvenSporadicStandard.RuStd.S2.ruThreeHex = String.ofList chars := by
  rw [chars, String.ofList_append, String.ofList_append, ← R3A.eq, ← R3B.eq, ← R3C.eq,
    CFSG.EvenSporadicStandard.RuStd.S2.ruThreeHex, String.append_assoc]

end CertificateChecks.KernelRuThree.R3

#kmisc_hexflat CertificateChecks.KernelRuThree.R3 CFSG.EvenSporadicStandard.RuStd.S2.ruThreeHex 3 4060 12 9
#ks_raworb CertificateChecks.KernelRuThree.S3R 4060 12 64 CFSG.EvenSporadicStandard.RuStd.S2.ruThreeArrs
  CertificateChecks.KernelRuThree.baseM 2 CertificateChecks.KernelRuThree.derivs

end
