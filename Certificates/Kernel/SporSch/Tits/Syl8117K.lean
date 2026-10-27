module

public import Certificates.Kernel.SporSch.Tits.Inv2266M
public import Certificates.Kernel.SporSch.Tits.Stab2270K
public import Certificates.Data.Kernel.SporSch.TitsSyl
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsInputs
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.TitsInvCheck
meta import CFSG.Sporadic.Schreier.TitsInvCheck

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsB1 11 CFSG.RankThree.PartTwo.Sec4.Item434RemTits.bOneArr

namespace CertificateChecks.KernelSporSch.TitsSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.PkPow
open CFSG.RankThree.PartTwo.Sec4.Item434RemTits
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAbel

@[expose] noncomputable def wS (wd : List Int) : Nat :=
  wordK 2925 12 (mask 12) (pidn 2925 12) TitsSS.T TitsSS.TI wd

theorem lX : lettersK 13 xWord = true := by quickRfl
theorem lY : lettersK 13 yWord = true := by quickRfl
theorem lZ : lettersK 13 zWord = true := by quickRfl

theorem rels : strictB (wK xWord) (fun X => strictB (wK yWord) (fun Y => strictB (wK zWord)
    (fun Z => rel3 1755 11 X Y Z))) = true := by quickRfl

theorem lines : strictB (wS xWord) (fun X => strictB (wS yWord) (fun Y => strictB (wS zWord)
    (fun Z => lines3 2925 12 X Y Z))) = true := by quickRfl

theorem bW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 bOneWord (wK bOneWord) =
    true := by
  unfold wordEqK
  quickRfl
theorem bB : Nat.beq (wK bOneWord) TitsB1 = true := by quickRfl
theorem cB : canonK 1755 11 (mask 11) (1755 * 11) TitsB1 = true := by quickRfl
theorem bNe : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsB1 = true := by quickRfl
theorem b3 : cube1 1755 11 TitsB1 = true := by quickRfl
theorem bT : Nat.beq (pc TitsB1 TitsT) (pc TitsT TitsB1) = true := by quickRfl
theorem kBN : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsN.LR TitsN.TRI TitsN.BP 5 0
    TitsB1 = true := by quickRfl

@[expose] noncomputable def QSyl : Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  fun _ => invTB TitsN.BP TitsT TitsB1

theorem negRelX : strictB (wK yWord) (fun Y => strictB (wK zWord)
    (fun Z => bIf(rel3 1755 11 (pidn 1755 11) Y Z, false, true))) = true := by quickRfl
theorem negRelZ : strictB (wK xWord) (fun X => strictB (wK yWord)
    (fun Y => bIf(rel3 1755 11 X Y Y, false, true))) = true := by quickRfl
theorem negLine : bIf(p513 (nfix 2925 12 (pidn 2925 12)), false, true) = true := by quickRfl
theorem negInv : bIf(invTB TitsN.BP (pidn 1755 11) (pidn 1755 11) TitsT (pidn 1755 11)
    (pidn 1755 11) (pidn 1755 11) (pidn 1755 11), false, true) = true := by quickRfl
theorem posInv : invTB TitsN.BP TitsT TitsB1 TitsT (pidn 1755 11) (pidn 1755 11) (pidn 1755 11)
    (pidn 1755 11) = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsSyl

end
