module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Data.TwinPerpV3A6iCurtisPerm
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

@[expose] noncomputable def curtisL (l : Fin 8 × Bool) : Nat :=
  Bool.rec (pinv (AP.S l.1.val)) (AP.S l.1.val) l.2

@[expose] noncomputable def curtisK (acc : Nat) (w : List (Fin 8 × Bool)) : Nat :=
  w.foldl (fun a l => pc a (curtisL l)) acc

theorem kCurtis : bAnd(allN 8 (fun i => bAnd(pm (AP.S i), cn (pinv (AP.S i)))),
    List.all curtisPG fun w => Nat.beq (curtisK pid w) pid) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
