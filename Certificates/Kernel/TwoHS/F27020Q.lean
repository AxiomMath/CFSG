module

public import Certificates.Kernel.TwoHS.F27020
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.LQT.C4126
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def ckBodyQ (I : Nat) (T A : Fin 6 → Nat) (E F : Fin 4 → Nat)
    (P : Fin 16 → Nat) : Bool :=
  bAnd((List.finRange 6).all (fun j => Nat.beq (pc (T j) (T j)) I),
  bAnd((List.finRange 6).all (fun k => Nat.beq (pc (A k) (A k)) I),
  bAnd((List.finRange 4).all (fun l => Nat.beq (E l) (F l)),
  bAnd((List.finRange 4).all (fun l => Nat.beq (pc (E l) (E l)) I),
  bAnd((List.finRange 4).all (fun l => (List.finRange 4).all fun l' =>
    (Nat.ble l'.val l.val || Nat.beq (pc (E l) (E l')) (pc (E l') (E l)))),
  dist16 P)))))

@[expose] noncomputable def ck27020Q (i : Fin 4) : Bool :=
  strictB idK fun I =>
  bind6 (fun j => EVK HYF HYF (hfxW i j)) fun T =>
  bind6 (fun k => EVK T T (hsCommWord k)) fun A =>
  bind4 (fun l => EVK HYF HYF (hfxE i l)) fun E =>
  bind4 (fun l => EVK A A (hfxE i l)) fun F =>
  bind16 (fun m => prodK E m.val) fun P =>
  ckBodyQ I T A E F P

end CFSG.KD.TwoHS

end
