module

public import Certificates.Kernel.HN1408.Tr2PDefs
public import Certificates.Kernel.HN1408.CbTData

public section

namespace CFSG.KD.HN1408.CbT

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408.Tr2

@[expose] noncomputable def nS : Nat := 2

@[expose] noncomputable def stab2Cnt (H : Nat) : Nat :=
  strictN H fun H => cnt2 672 120 T0 T1 fun A B => comm2 1401 A B H

@[expose] noncomputable def stab2K (H n : Nat) : Bool := Nat.beq (stab2Cnt H) n

end CFSG.KD.HN1408.CbT

end
