module

public import Certificates.Data.Kernel.Spor.WordProg
public import Certificates.Data.Kernel.Spor.WordProgW
public import Certificates.Kernel.Fi23M.Data
public import Certificates.Kernel.Fi23Pf.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi23Pf

theorem lists : (CFSG.KC.WP.statesOK (nat_lit 2) WC PS (nat_lit 18) &&
    CFSG.KC.WP.relProgsOK (nat_lit 2) (nat_lit 18) PE (nat_lit 21) &&
    CFSG.KC.WP.relProgsOK (nat_lit 2) (nat_lit 18) PF (nat_lit 21)) = true := by
  quickRfl

@[expose] def sC (k : Nat) : Bool :=
  CFSG.KC.Ord.progOK CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PS k) (RS k)

@[expose] def eC (j : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PE j))
    (CFSG.KC.Ord.progTop CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PF j))

theorem n01 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS (nat_lit 0)) (RS (nat_lit 1))) =
    true := by
  quickRfl

theorem n02 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS (nat_lit 0)) (RS (nat_lit 2))) =
    true := by
  quickRfl

theorem n12 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS (nat_lit 1)) (RS (nat_lit 2))) =
    true := by
  quickRfl

end CFSG.KD.Fi23Pf

#kc_each CFSG.KD.Fi23Pf.sC 0 18

#kc_each CFSG.KD.Fi23Pf.eC 0 21

namespace CFSG.KD.Fi23Pf

#kc_forall_chunks S.all (fun k => sC k = true) 18 CFSG.KD.Fi23Pf.sC 1

#kc_forall_chunks E.all (fun j => eC j = true) 21 CFSG.KD.Fi23Pf.eC 1

end CFSG.KD.Fi23Pf

end
