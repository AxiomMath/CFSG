module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.PartOne.KS.RuFiveCheckInputs
public meta import CFSG.RankThree.PartOne.KS.RuFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.RankThree.Native.HSMcLFiveCheck
public import CFSG.RankThree.Native.HSMcLFiveCheck
public import CFSG.Sporadic.Schreier.RuDefs
public meta import CFSG.Sporadic.Schreier.RuDefs
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuFive

meta def base0M : Array Nat := CFSG.RankThree.PartOne.ruCase0BaseArr

meta def base1M : Array Nat := CFSG.RankThree.PartOne.ruCase1BaseArr

@[expose] def derivs0 : List (List Int) := CFSG.RankThree.PartOne.ruCase0Words.toList.drop 2

@[expose] def derivs1 : List (List Int) := CFSG.RankThree.PartOne.ruCase1Words.toList.drop 2

end CertificateChecks.KernelRuFive

#ks_chars CertificateChecks.KernelRuFive.H50 CFSG.RankThree.PartOne.ruCase0Hex
#kmisc_hexflat CertificateChecks.KernelRuFive.H50 CFSG.RankThree.PartOne.ruCase0Hex 3 4060 12 8
#ks_chars CertificateChecks.KernelRuFive.H51 CFSG.RankThree.PartOne.ruCase1Hex
#kmisc_hexflat CertificateChecks.KernelRuFive.H51 CFSG.RankThree.PartOne.ruCase1Hex 3 4060 12 10
#ks_raworb CertificateChecks.KernelRuFive.S50 4060 12 64 CFSG.RankThree.PartOne.ruCase0Arrs
  CertificateChecks.KernelRuFive.base0M 2 CertificateChecks.KernelRuFive.derivs0
#ks_raworb CertificateChecks.KernelRuFive.S51 4060 12 64 CFSG.RankThree.PartOne.ruCase1Arrs
  CertificateChecks.KernelRuFive.base1M 2 CertificateChecks.KernelRuFive.derivs1

end
