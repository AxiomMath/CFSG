module

public import Certificates.Kernel.HN1408.TabXCntDefs

public section

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408.CzT CFSG.KD.HN1408.TabX

@[expose] noncomputable def comm3 (A B H : Nat) : Bool :=
  bAnd(commB A B H (pt A (pt B 0)) (pt A (pt B 1)),
    Nat.beq (pt A (pt B (pt H 2))) (pt H (pt A (pt B 2))))

@[expose] noncomputable def stab3Cnt (H : Nat) : Nat :=
  strictN H fun H => czCnt T0 T1 fun A B => comm3 A B H

@[expose] noncomputable def stab3K (H n : Nat) : Bool := Nat.beq (stab3Cnt H) n

end CFSG.KD.HN1408.Tab6

end
