module

public import Certificates.Kernel.RouteP.Data.Pres
public import Certificates.Kernel.RouteP.Data.Y332
public import Certificates.Kernel.RouteP.Text.Data

public section

namespace CFSG.KD.RouteP

open CFSG.KC.RouteP CFSG.KC.Fi24Net

@[expose] noncomputable def lkck (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (g : Nat) : Bool :=
  bIf(Nat.blt g (nat_lit 38),
    genOK CG (NW (Nat.div g (nat_lit 19))) (Nat.mul (nat_lit 32) (Nat.div g (nat_lit 19)))
      (Nat.mod g (nat_lit 19)),
    bIf(Nat.beq g (nat_lit 38), kapLinkOK CG (KA (nat_lit 0)) (nat_lit 19),
      bIf(Nat.beq g (nat_lit 39), kapLinkOK CG (KB (nat_lit 0)) (nat_lit 20),
        bIf(Nat.beq g (nat_lit 40), kapLinkOK CG (KA (nat_lit 1)) (nat_lit 51),
          kapLinkOK CG (KB (nat_lit 1)) (nat_lit 52)))))

@[expose] noncomputable def lkP (g : Nat) : Bool := lkck NWP KAP KBP g

@[expose] noncomputable def lkO (g : Nat) : Bool := lkck NWO KAO KBO g

@[expose] noncomputable def lkY (g : Nat) : Bool := lkck NWY KAY KBY g

end CFSG.KD.RouteP

end
