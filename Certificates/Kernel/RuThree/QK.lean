module

public import Certificates.Kernel.RuThree.QData
public import Certificates.Kernel.RuThree.Chain
public import Certificates.Data.Kernel.LinesPK
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CFSG.KC.LinesPK
  CFSG.KC.FiveLocK CFSG.EvenSporadicStandard.RuStd.S2

theorem kQW : allN 2 (fun k => wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11
    (qWords.getD k []) (QGP k)) = true := by
  quickRfl

theorem kLW : allN 13 (fun k => wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11
    (ruThreeLineWords.getD k []) (LNP k)) = true := by
  quickRfl

theorem kTW : allN 13 (fun k => wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11
    (ruThreeTransWords.getD k []) (TRP k)) = true := by
  quickRfl

theorem kQP : allN 2 (fun k => permB 4060 12 (QGP k)) = true := by quickRfl

theorem kLP : allN 13 (fun k => permB 4060 12 (LNP k)) = true := by quickRfl

theorem kRQ : Nat.beq RQ.N 27 = true ∧ Nat.beq RQ.ng 2 = true ∧
    allN 2 (fun k => Nat.beq (RQ.G k) (QGP k)) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem kRQP : allN 27 (fun i => permB 4060 12 (RQ.T i)) = true := by quickRfl

theorem kLines : linesPK 4060 12 3 27 13 RQ.T RQ.S LNP = true := by quickRfl

theorem kTrans : transFK 4060 12 13 TRP LNP ruThreeRec = true := by quickRfl

end CertificateChecks.KernelRuThree

end
