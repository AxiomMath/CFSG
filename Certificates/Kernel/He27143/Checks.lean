module

public import Certificates.Kernel.HeTab.Data
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Data.Kernel.HeTabK
import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

public section

namespace CFSG.KD.HeTab

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KC.HeTab CFSG.KD.HeOrb CFSG.EvenSporadicStandard.Induction

@[expose] noncomputable def wSel (k : Nat) : (Nat → Nat) × List Int :=
  List.getD [(WX, heWordE1), (WY, heWordE2), (WZ, heWordE3)] k (WX, heWordE1)

@[expose] noncomputable def famW (c : Nat) : Bool :=
  strictB (Nat.div c (nat_lit 9)) fun k => strictB (Nat.mul (nat_lit 1000) (Nat.mod c (nat_lit 9)))
    fun lo => allN (nat_lit 1000) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 8330), wordK AL BE BI (wSel k).1 (wSel k).2 x, true)

theorem inv_ok : allN (nat_lit 8330) (invBK BE BI) = true := by quickRfl

theorem e8_ok : allN (nat_lit 8330) (e8K WX WY WZ) = true := by quickRfl

theorem ne_ok : (movesK (r32 WX) id && movesK (r32 WY) id && movesK (r32 WY) (r32 WX) &&
    movesK (r32 WZ) id && movesK (r32 WZ) (r32 WX) && movesK (r32 WZ) (r32 WY) &&
    movesK (r32 WZ) (fun x => r32 WX (r32 WY x))) = true := by quickRfl

end CFSG.KD.HeTab

#kss_each CFSG.KD.HeTab.W CFSG.KD.HeTab.famW 27

end
