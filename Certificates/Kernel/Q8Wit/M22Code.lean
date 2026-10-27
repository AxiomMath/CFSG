module

public import Certificates.Data.TwinPerpSmSp1WitM22
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.Monster.Code.Defs
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelQ8W.M22

open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.RankTwoSporadic.M22
open Certificates.TwinPerpSmSp1

theorem inX : allLt m22Wit.xg.size (fun l => m22InX m22Wit.xg[l]!) = true := by
  decide +kernel

theorem pairS : allLt m22Wit.syl.pg.size (fun l => pairA m22Wit.syl.pg[l]!) = true := by
  decide +kernel

end CertificateChecks.KernelQ8W.M22

end
