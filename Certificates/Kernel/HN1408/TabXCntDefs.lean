module

public import Certificates.Kernel.HN1408.CzTScanDefs
public import Certificates.Data.Kernel.Spor.BaseEq
public import Certificates.Kernel.HN1408.CzTData

public section

namespace CFSG.KD.HN1408.TabX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.BaseEq CFSG.KD.HN1408.CzT

@[expose] noncomputable def czCnt (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => strictN ih fun a =>
      Nat.add a (strictN (T0 i) fun A => cntN 24 fun j => F A (T1 j))) 1280

@[expose] noncomputable def stabCnt (H : Nat) : Nat :=
  strictN H fun H => czCnt T0 T1 fun A B => commB A B H (pt A (pt B 0)) (pt A (pt B 1))

@[expose] noncomputable def stabK (H n : Nat) : Bool := Nat.beq (stabCnt H) n

end CFSG.KD.HN1408.TabX

end
