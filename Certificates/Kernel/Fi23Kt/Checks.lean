module

public import Certificates.Data.Kernel.Spor.WordProg
public import Certificates.Data.Kernel.Spor.WordProgW
public import Certificates.Kernel.Fi23M.Data
public import Certificates.Kernel.Fi23Kt.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.Fi23Kt

theorem lists : (CFSG.KC.WP.statesOK (nat_lit 2) WC PS (nat_lit 15) &&
    CFSG.KC.WP.relProgsOK (nat_lit 2) (nat_lit 15) PE (nat_lit 41) &&
    CFSG.KC.WP.relProgsOK (nat_lit 2) (nat_lit 15) PF (nat_lit 41)) = true := by
  quickRfl

@[expose] def kt27301sC (k : Nat) : Bool :=
  CFSG.KC.Ord.progOK CFSG.KD.Fi23M.RB 2 RS CFSG.KD.Fi23M.MUL CFSG.KD.Fi23M.ONE (PS k) (RS k)

@[expose] def kt27301eC (j : Nat) : Bool :=
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

end CFSG.KD.Fi23Kt

#kc_each CFSG.KD.Fi23Kt.kt27301sC 0 15

#kc_each CFSG.KD.Fi23Kt.kt27301eC 0 41

namespace CFSG.KD.Fi23Kt

#kc_forall_chunks S.all (fun k => kt27301sC k = true) 15 CFSG.KD.Fi23Kt.kt27301sC 1

#kc_forall_chunks E.all (fun j => kt27301eC j = true) 41 CFSG.KD.Fi23Kt.kt27301eC 1

end CFSG.KD.Fi23Kt

end
