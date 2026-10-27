module

public import Certificates.Data.Kernel.Fi23K.Defs
public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Kernel.Fi23K.Tabs

public section

namespace CFSG.KD.Fi23K

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.KC.Fi23K

@[expose] noncomputable def tabList (r : Nat) : Nat → Nat → List UInt32
  | _, 0 => []
  | j, c + 1 => UInt32.ofNat (tb G r j) :: tabList r (j + 1) c

@[expose] noncomputable def tabOf (r : Nat) : Table := ⟨tabList r 0 31671⟩

@[expose] noncomputable def keyW : Nat → Nat → Array W
  | 0, _ => matD
  | f + 1, k =>
    if k = 0 then matD
    else if tb G 92 k = 1 then conjW 253 matA matA (keyW f (tb G 91 k))
    else conjW 253 matB matBi (keyW f (tb G 91 k))

@[expose] noncomputable def orbLit : WOrbit :=
  ⟨Array.ofFn (n := 31671) fun k => keyW 200 k.val, tabOf 39, tabOf 40, tabOf 91, tabOf 92⟩

end CFSG.KD.Fi23K

end
