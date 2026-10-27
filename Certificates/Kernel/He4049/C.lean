module

public import Certificates.Kernel.He4049.T
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He4049

open CFSG.KC.Enum CFSG.KS.Prim

theorem canonA : canonK 8330 14 16383 116620 (TF 0) = true := by quickRfl

theorem bindA : allN 8330 (fun i => Nat.beq (pg 14 16383 (TF 0) i) (pg 14 16383 (TF 0) i)) = true := by
  quickRfl

theorem canonB : canonK 8330 14 16383 116620 (TF 1) = true := by quickRfl

theorem bindB : allN 8330 (fun i => Nat.beq (pg 14 16383 (TF 1) i) (pg 14 16383 (TF 1) i)) = true := by
  quickRfl

theorem valid : CFSG.QuasithinUnique.K1.SporadicPerm.slpValidAux progX 2 = true := by
  decide +kernel

theorem len : progX.length = 341 := by decide +kernel

end CFSG.KD.He4049

end
