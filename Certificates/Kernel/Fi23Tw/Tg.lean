module

public import Certificates.Kernel.Fi23Tw.ChkDefs
import CFSG.Certificates.Kernel.BabyMonster.Load

public section

namespace CFSG.KD.Fi23Tw

open CFSG.KC.Enum CFSG.KC.Fi23R CFSG.KC.Fi23Tw CFSG.KD.Fi23K

@[expose] noncomputable def tgHeads : List Nat := TG.map fun g => nthL g (nat_lit 0)

@[expose] noncomputable def tgc : Bool :=
  allN (nat_lit 6) fun t => Nat.beq (nthL tgHeads t) (tA G (nat_lit 4) t)

@[expose] noncomputable def first : Bool :=
  allN (nat_lit 135) fun i => List.rec (motive := fun _ => Bool) false
    (fun e _ ih => bIf(Nat.beq (Nat.div (Nat.land e (nat_lit 32767)) (nat_lit 135)) i, true, ih)) PE

end CFSG.KD.Fi23Tw

end

#bm_bool CFSG.KD.Fi23Tw ch17340tgc_ok (tgc)
#bm_bool CFSG.KD.Fi23Tw ch17340first_ok (first)
