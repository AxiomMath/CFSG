module

public import Certificates.Kernel.He7222.KChK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain

@[expose] noncomputable def kbK (B : List Nat) : Bool :=
  allN (lenS B) (fun i => Nat.blt (getS B i) 8330)

@[expose] noncomputable def lprodK (T : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1) (fun t _ ih => Nat.mul (lenS t) ih) T

theorem ch7222kb : (kbK (getLs a0QBase 0) && kbK (getLs a0QBase 1) && kbK (getLs t1QBase 0) &&
    kbK (getLs t1QBase 1) && kbK (getLs t1QBase 2) && kbK (getLs t1QBase 3) &&
    kbK (getLs t1QBase 4)) = true := by
  quickRfl

theorem ch7222kn : (Nat.beq (Nat.mul (lenS (getLs a0CKeys 0))
      (lprodK [a0K0T0, a0K0T1, a0K0T2, a0K0T3, a0K0T4, a0K0T5])) 161280 &&
    Nat.beq (Nat.mul (lenS (getLs a0CKeys 1))
      (lprodK [a0K1T0, a0K1T1, a0K1T2, a0K1T3, a0K1T4, a0K1T5])) 161280 &&
    Nat.beq (Nat.mul (lenS (getLs t1CKeys 1))
      (lprodK [t1K0T0, t1K0T1, t1K0T2, t1K0T3, t1K0T4])) 21504 &&
    Nat.beq (Nat.mul (lenS (getLs t1CKeys 2))
      (lprodK [t1K1T0, t1K1T1, t1K1T2, t1K1T3, t1K1T4])) 21504 &&
    Nat.beq (Nat.mul (lenS (getLs t1CKeys 3))
      (lprodK [t1K2T0, t1K2T1, t1K2T2, t1K2T3, t1K2T4])) 21504 &&
    Nat.beq (Nat.mul (lenS (getLs t1CKeys 5))
      (lprodK [t1K3T0, t1K3T1, t1K3T2, t1K3T3, t1K3T4, t1K3T5])) 21504 &&
    Nat.beq (Nat.mul (lenS (getLs t1CKeys 6))
      (lprodK [t1K4T0, t1K4T1, t1K4T2, t1K4T3, t1K4T4, t1K4T5])) 21504) = true := by
  quickRfl

end CFSG.KD.He7222

end
