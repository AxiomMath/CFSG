module

public import Certificates.Kernel.Fi23P.ChkDefs
public import Certificates.Data.Kernel.Fi23R.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23R

set_option Elab.async false

theorem cnt_ok0 : Nat.beq (cntS (fun p => Nat.beq (labP p) (nat_lit 0)) (nat_lit 0) (nat_lit 31671))
    (nat_lit 255) = true := by quickRfl
theorem cnt_ok1 : Nat.beq (cntS (fun p => Nat.beq (labP p) (nat_lit 1)) (nat_lit 0) (nat_lit 31671))
    (nat_lit 13056) = true := by quickRfl
theorem cnt_ok2 : Nat.beq (cntS (fun p => Nat.beq (labP p) (nat_lit 2)) (nat_lit 0) (nat_lit 31671))
    (nat_lit 18360) = true := by quickRfl

end CFSG.KD.Fi23P

end
