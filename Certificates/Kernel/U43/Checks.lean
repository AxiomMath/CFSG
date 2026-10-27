module

public import Certificates.Data.Kernel.U43.Defs
public import Certificates.Data.Kernel.G2Three.Syl
public import Certificates.Kernel.U43.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.U43

open CFSG.KC.Loop CFSG.KD.G2Three CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem u43Letters_ok : lettersK UA = true := by quickRfl

theorem u43Gens_ok : allBelow 3 1 (fun s => Nat.beq (UG s) (wordP UA (uGenWords.getD s []))) =
    true := by quickRfl

theorem u43One_ok : Nat.beq (UX 0) ONE4 = true := by quickRfl

theorem u43Par_ok : parK UX UG 3 uPar 0 = true := by quickRfl

theorem u43Close_ok : closeU UX UG (fR (UPOS 0)) 729 3 35 = true := by quickRfl

theorem u43Sort_ok : sortK UX USRT USRI 729 12 = true := by quickRfl

theorem u43Bad_ok : allBelow 12 1 (badK UX UA UKW) = true := by quickRfl

end CFSG.KD.U43

end
