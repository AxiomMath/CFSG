module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
public meta import CFSG.RankThree.PartOne.KS.HeSevenCheckDefs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Mathlib
public import Mathlib

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

meta def base2M : Array Nat := CFSG.RankThree.PartOne.heSevenCase2BaseArr

@[expose] def derivs2 : List (List Int) := CFSG.RankThree.PartOne.heSevenCase2Words.toList.drop 3

end CertificateChecks.KernelHeLoc.Seven

#ks_chars CertificateChecks.KernelHeLoc.S72T CFSG.RankThree.PartOne.heSevenCase2Hex
#kmisc_hexflat CertificateChecks.KernelHeLoc.S72T CFSG.RankThree.PartOne.heSevenCase2Hex 4 8330 14 10
#ks_raworb CertificateChecks.KernelHeLoc.S72 8330 14 64 CFSG.RankThree.PartOne.heSevenCase2Arrs
  CertificateChecks.KernelHeLoc.Seven.base2M 3 CertificateChecks.KernelHeLoc.Seven.derivs2

end
