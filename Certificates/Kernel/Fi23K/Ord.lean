module

public import Certificates.Kernel.Fi23K.ChkDefs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def ordK : Bool :=
  allN (nat_lit 31671) fun k => bAnd(Nat.beq (tb G (nat_lit 39) (tb G (nat_lit 39) k)) k,
    Nat.beq (tb G (nat_lit 40) (tb G (nat_lit 40) (tb G (nat_lit 40) k))) k)

set_option Elab.async false

theorem ord_ok : ordK = true := by quickRfl

theorem neg_beta_sq : Bool.not (allN (nat_lit 31671) fun k =>
    Nat.beq (tb G (nat_lit 40) (tb G (nat_lit 40) k)) k) = true := by quickRfl

end CFSG.KD.Fi23K

end
