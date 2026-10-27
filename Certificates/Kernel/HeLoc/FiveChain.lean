module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public meta import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
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

namespace CertificateChecks.KernelHeLoc.FiveL

meta def base0M : Array Nat := CFSG.RankThree.PartOne.heFiveCase0BaseArr

@[expose] def derivs0 : List (List Int) := CFSG.RankThree.PartOne.heFiveCase0Words.toList.drop 3

end CertificateChecks.KernelHeLoc.FiveL

#ks_chars CertificateChecks.KernelHeLoc.S50T CFSG.RankThree.PartOne.heFiveCase0Hex
#kmisc_hexflat CertificateChecks.KernelHeLoc.S50T CFSG.RankThree.PartOne.heFiveCase0Hex 4 8330 14 11
#ks_raworb CertificateChecks.KernelHeLoc.S50 8330 14 64 CFSG.RankThree.PartOne.heFiveCase0Arrs
  CertificateChecks.KernelHeLoc.FiveL.base0M 3 CertificateChecks.KernelHeLoc.FiveL.derivs0

end
