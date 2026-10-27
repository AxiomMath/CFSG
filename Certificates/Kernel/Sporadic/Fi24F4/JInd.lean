module

public import Certificates.Kernel.Sporadic.Fi24F4.JC
import CFSG.Certificates.Kernel.Common.SliceRange
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.KD.Fi24F4

@[expose] noncomputable def indS (s : Nat) : Bool :=
  CFSG.KC.Enum.allN 81 (fun d => CFSG.KC.orB (Nat.beq (Nat.add (Nat.mul s 81) d) 0)
    (indc (Nat.add (Nat.mul s 81) d)))

end CFSG.KD.Fi24F4

#kc_slice_range CFSG.KD.Fi24F4.indS CFSG.KD.Fi24F4.Ck.indS 0 3

end
