module

public import Certificates.Kernel.HN1408.SylS
public import Certificates.Data.Kernel.Spor.BaseEq
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask CFSG.KS.BaseEq

@[expose] noncomputable def syGen (j : Nat) : Nat := r32 SylS.POS j

@[expose] noncomputable def syCenHd : Bool :=
  allN 5 (fun j => bAnd(Nat.blt (syGen j) 2048, Nat.beq (SylS.T (syGen j)) (SylS.G j)))

@[expose] noncomputable def syCenPt (k i : Nat) : Bool :=
  allN k (fun j => commKeyK 11 (mask 11) 2 0 SylS.T i (syGen (Nat.sub 5 (Nat.succ j))))

theorem syCen_hd : syCenHd = true := by quickRfl

theorem syCen_cnt : Nat.beq (cntN 2048 (syCenPt 5)) 4 = true := by quickRfl

end CFSG.KD.HN1408

end
