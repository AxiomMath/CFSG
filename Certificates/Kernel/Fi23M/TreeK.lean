module

public import Certificates.Kernel.Fi23K.ChkDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def trAt (k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), true, strictB (tb G (nat_lit 91) k) fun p => bAnd(Nat.blt p k,
    bIf(Nat.beq (tb G (nat_lit 92) k) (nat_lit 1), Nat.beq (tb G (nat_lit 39) p) k,
      bAnd(Nat.beq (tb G (nat_lit 92) k) (nat_lit 2), Nat.beq (tb G (nat_lit 40) p) k))))

@[expose] noncomputable def trK : Bool := allN (nat_lit 31671) trAt

set_option Elab.async false

theorem tree_ok : trK = true := by quickRfl

end CFSG.KD.Fi23K

end
