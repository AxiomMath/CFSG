module

public import Certificates.Kernel.He7222.Data
public import Certificates.Data.Kernel.OrbRow.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.He7222

open CFSG.KC.OrbRow

@[expose] noncomputable def incK (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih b => Bool.rec (motive := fun _ => Bool) false (ih x) (Nat.blt b x)) L

@[expose] noncomputable def incAll (LL : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun L _ ih => Bool.rec (motive := fun _ => Bool) false ih (incK L (nat_lit 0))) LL

theorem ch7222keys : (incAll a0CKeys && incAll t1CKeys && Nat.beq (lenS (List.map lenS a0CKeys))
    5 && Nat.beq (lenS (List.map lenS t1CKeys)) 7) = true := by
  quickRfl

end CFSG.KD.He7222

end
