module

public import Certificates.Data.Kernel.Misc.G23F3
public import CFSG.LieType.Multipliers.G23Data

public section

namespace CFSG.KD.Misc.G23F3

open CFSG.KC.Misc.G23F3 CFSG.LieType.Multipliers.G23

@[expose] noncomputable def codeOf (A : Array (Array Nat)) : List Nat :=
  (List.range 196).map fun t => (A[t / 14]!)[t % 14]!

@[expose] noncomputable def RK : List Nat :=
  (List.finRange 4).map fun j => pkK (codeOf (rootArr j))

@[expose] noncomputable def SK (w : List (Fin 4)) : Nat := wordK RK (w.map Fin.val)

end CFSG.KD.Misc.G23F3

end
