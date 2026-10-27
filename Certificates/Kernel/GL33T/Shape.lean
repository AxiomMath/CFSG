module

public import Certificates.Data.Kernel.GL33TShape
public import Certificates.Kernel.GL33T.Data

public section

namespace CFSG.KD.GL33T

open CFSG.KC.GL33T

@[expose] noncomputable def shapeC (i : Nat) : Bool :=
  shapeK (List.getD gens i []) (List.getD kind i 9) (List.getD ch i [])

theorem ch799501shape : uptoK shapeC 48 = true := by decide +kernel

theorem ch799501shape_neg_gen : (!shapeK [0] 3 []) = true := by decide +kernel

theorem ch799501shape_neg_kind : (!shapeK [] 1 [[(2, 0, [[0]])]]) = true := by decide +kernel

theorem ch799501shape_neg_word : (!shapeK [] 3 [[(3, 0, [])]]) = true := by decide +kernel

end CFSG.KD.GL33T

end
