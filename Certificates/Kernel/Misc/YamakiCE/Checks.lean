module

public import Certificates.Data.Kernel.Misc.YamakiCE
public import Certificates.Data.Kernel.Misc.YamakiGenPos
public import Certificates.Kernel.Misc.YamakiRep.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.YamakiCE

open CFSG.KD.YamakiRep CFSG.KD.YamakiGenPos CFSG.KD.YamakiA0
  CFSG.ClassicalInvolution.Sp62Rec

@[expose] def posV0E : List Nat := [9702, 7255, 6751, 9985, 13]

@[expose] def posWE : List Nat := [10804, 11323, 0, 1, 6103, 10634, 4107, 1, 0, 10143]

theorem ch550823pV : genPosK RE 14 11520 v0Idx posV0E = true := by quickRfl

theorem ch550823pW :
    numPosK RE 14 11520 ((commFixers ++ commConjs ++ commTriple).map (wordN RE)) posWE = true := by
  quickRfl

theorem ch550823sq : sqK RV 17 32 = true := by quickRfl

theorem ch550823cj : v0ConjK RV 17 = true := by quickRfl

theorem ch550823gk : commGkK RV 17 = true := by quickRfl

theorem ch550823fx : commFixK RV 17 commFixers = true := by quickRfl

theorem ch550823tr : commTripleK RV = true := by quickRfl

theorem ch550823ex : commExprK RV = true := by quickRfl

theorem ch550823bV : (List.range 12).all (fun j => Nat.blt (RV j) (2 ^ 36)) = true := by quickRfl

theorem ch550823bH : (List.range 12).all (fun j => Nat.blt (RH j) (2 ^ 36)) = true := by quickRfl

end CFSG.KD.YamakiCE

end
