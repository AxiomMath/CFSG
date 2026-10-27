module

public import Certificates.Kernel.O8Sq.Wit
public import Certificates.Kernel.O8Sq.Forest
public import Certificates.Kernel.O8Sq.Chain
public import Certificates.Kernel.OmegaEight.E4O8CentK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Sq

open CFSG.KC.Enum CFSG.KS CFSG.KC.PCent CFSG.KC.O8Sq CertificateChecks.KernelO8
  CertificateChecks.KernelO8.E4C CFSG.ClassicalInvolution.O8Data CFSG.KC.Misc.ArrEnum CFSG.KS.Raw

@[expose] noncomputable def wdJ (j : Nat) : List Int :=
  (witWords.getD (IW.getD j (0, 0)).1 []).getD (IW.getD j (0, 0)).2 []

theorem ch272020lt : bAnd(e4Lets 4 RW, bAnd(e4Lets 10 HW, bAnd(e4Lets 8 P1, e4Lets 8 P2))) =
    true := by
  quickRfl

theorem ch272020o : allN 57 (fun j => strictB (repW j) (fun r =>
    bAnd(Nat.beq (pc9 (pc9 r r) (pc9 r r)) pid, bIf(Nat.beq (pc9 r r) pid, false, true)))) =
    true := by
  quickRfl

theorem ch272020ww : allN 57 (fun j => bAnd(lettersK 17 (wdJ j),
    bAnd(CFSG.Monster.B.Co2.Native.lettersOK 17 (wdJ j), permB 360 9 (wO (wdJ j))))) = true := by
  quickRfl

theorem ch272020gw : bAnd(allN 3 (fun j => bAnd(lettersK 17 ((centGens.getD 1 []).getD j []),
    CFSG.Monster.B.Co2.Native.lettersOK 17 ((centGens.getD 1 []).getD j []))),
    bAnd(allN 3 (fun j => bAnd(lettersK 17 ((centGens.getD 2 []).getD j []),
    CFSG.Monster.B.Co2.Native.lettersOK 17 ((centGens.getD 2 []).getD j []))),
    bAnd(allN 6 (fun k => permB 360 9 (G1.getD k 0)), allN 6 (fun k => permB 360 9 (G2.getD k 0)))))
    = true := by
  quickRfl

end CertificateChecks.KernelO8Sq

end
