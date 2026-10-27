module

public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.B3S3.Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib
public import Mathlib

public section

namespace CertificateChecks.KernelRuThree

open CFSG.EvenSporadicStandard.RuStd.S2

@[expose] def qWords : List (List Int) := [[-9], [10, 11, 4, 3, 7, 6, -10, 8, 9]]

meta def qgM : Array (Array Nat) := ruThreeQGens

meta def lnM : Array (Array Nat) := ruThreeLines

meta def trM : Array (Array Nat) := ruThreeTransporters

end CertificateChecks.KernelRuThree

end

#kmisc_packarrs CertificateChecks.KernelRuThree.QGP CertificateChecks.KernelRuThree.qgM 12
#kmisc_packarrs CertificateChecks.KernelRuThree.LNP CertificateChecks.KernelRuThree.lnM 12
#kmisc_packarrs CertificateChecks.KernelRuThree.TRP CertificateChecks.KernelRuThree.trM 12
#kb3_enum CertificateChecks.KernelRuThree.RQ CFSG.EvenSporadicStandard.RuStd.S2.ruThreeQGens
  CFSG.EvenSporadicStandard.RuStd.S2.ruThreeBaseArr 4060 12
