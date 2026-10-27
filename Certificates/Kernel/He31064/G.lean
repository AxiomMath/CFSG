module

public import Certificates.Kernel.He31064.M
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He31064

open CFSG.KC.DcTup

@[expose] noncomputable def spl (w : List Nat) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 251)
    (fun l _ ih i => Nat.blt i 251 && Nat.beq (nthD (0, 0) xp i).1 l && ih (nthD (0, 0) xp i).2)
    w i

namespace CG

open CFSG.KS.PEnum

theorem abA : allN 8330 (fun p => Nat.beq (im (nth ab 0) p) (r32 CFSG.KD.HeOrb.AL p)) = true := by
  quickRfl
theorem abB : allN 8330 (fun p => Nat.beq (im (nth ab 1) p) (r32 CFSG.KD.HeOrb.BE p)) = true := by
  quickRfl
theorem spell : allN 133 (fun j => spl (W j) (nth ri j)) = true := by quickRfl
theorem npairs : Nat.beq (lenK pairs) 78 = true := by quickRfl

end CG

end CFSG.KD.He31064

end
