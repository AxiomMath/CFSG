module

public import Certificates.Kernel.SporSch.Tits.Five10050D
public import Certificates.Kernel.SporSch.Tits.Abel2261
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.RankThree.PartOne.KE
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem fW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 titsFiveWord
    (wK titsFiveWord) = true := by
  unfold wordEqK
  quickRfl
theorem fB : Nat.beq (wK titsFiveWord) TitsF = true := by quickRfl
theorem cF : C TitsF := by quickRfl
theorem kFH : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 TitsF =
    true := by quickRfl
theorem kFne : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsF = true := by quickRfl
theorem kF5 : Nat.beq (pc (pc (pc (pc TitsF TitsF) TitsF) TitsF) TitsF) (pidn 1755 11) = true := by
  quickRfl
theorem cntF : Nat.beq (popc (tot5 TitsH.LR) TitsMF.M) 10 = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsFive

end
