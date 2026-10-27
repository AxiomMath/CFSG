module

public import Certificates.Kernel.OmegaEight.E9KData
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E9K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
open CertificateChecks.KernelO8

theorem perm : allN 8 (fun k => permB 360 9 (OmP.S k)) = true := by quickRfl

theorem nums : (Nat.beq E9Q.ng 3 && Nat.beq E9Q.N 243 && Nat.beq E9D.ng 4 && Nat.beq E9D.N 81)
    = true := by quickRfl

theorem idK : Nat.beq (CFSG.KC.BfsPin.keyK 360 9 ps (pidn 360 9)) idKey = true := by quickRfl

theorem keysQ : keysSK 360 9 ps E9Q.N E9Q.T E9Q.SK = true := by quickRfl

theorem keysD : keysSK 360 9 ps E9D.N E9D.T E9D.SK = true := by quickRfl

theorem lettersQ : (o8pE9.qW.toList.all fun w => w.all fun l => decide (l < 8)) = true := by
  simp only [o8pE9, Array.toList_map]
  decide +kernel

theorem lettersH : (o8pE9.hW.toList.all fun w => w.all fun l => decide (l < 8)) = true := by
  simp only [o8pE9, Array.toList_map]
  decide +kernel

theorem lettersD : (o8pE9.dW.toList.all fun w => w.all fun l => decide (l < 3)) = true := by
  simp only [o8pE9, Array.toList_map]
  decide +kernel

theorem wordsQ : o8pE9.qW.toList.map (posWordK 360 9 OmP.S) = (List.range 3).map E9Q.G := by
  simp only [o8pE9, Array.toList_map]
  decide +kernel

theorem wordsD : o8pE9.dW.toList.map (posWordK 360 9 E9Q.G) = (List.range 4).map E9D.G := by
  simp only [o8pE9, Array.toList_map]
  decide +kernel

theorem wordsH : o8pE9.hW.toList.map (posWordK 360 9 OmP.S) = (List.range 4).map E9H := by
  simp only [o8pE9, Array.toList_map]
  decide +kernel

theorem elem : allN 4 (fun a => Nat.beq (pm (E9D.G a) (pm (E9D.G a) (E9D.G a))) (pidn 360 9) &&
    allN 4 fun b => Nat.beq (pm (E9D.G a) (E9D.G b)) (pm (E9D.G b) (E9D.G a))) = true := by
  quickRfl

theorem cw : allN 972 cwOK = true := by quickRfl

theorem pairs : allN 243 (fun a => allN 243 (pairK a)) = true := by quickRfl

end CertificateChecks.KernelO8.E9K

end
