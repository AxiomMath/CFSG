module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Data.Th687.MFactsA
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep
  CFSG.Sporadic.Th.Recog.MFactsData

@[expose] def sqGT : TE := .word sqrtWord
@[expose] def sqGiT : TE := .word sqrtWordInv
@[expose] def sqMT : TE := .mul (.mul (.mul sqGiT (.word dWord)) sqGT) (.nf 84)

@[expose] def l687003 : List (TE × TE × Bool) :=
  [(.mul sqGiT sqGT, .one, true), (.mul sqMT sqMT, .z, true),
    (.mul sqMT (.q 0), .mul (.q 0) sqMT, true), (.q 0, .one, false), (.q 0, .z, false)]

theorem ok687003 : pairsOK thK l687003 = true := by quickRfl

theorem cent_card : centPairCard () = 2 ^ 8 := by decide +kernel

theorem inv_card : invPairCard () = 143 := by decide +kernel

theorem invQ_card : invQCard () = 270 := by decide +kernel

end CertificateChecks.KernelTh.Fam

end
