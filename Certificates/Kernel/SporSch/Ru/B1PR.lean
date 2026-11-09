module

public import Certificates.Kernel.SporSch.Ru.B1X
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
  CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def pairCondK (A B : Nat) : Bool :=
  !Nat.beq B Z && !Nat.beq B A && !Nat.beq B (pc Z A) && Nat.beq (pc A B) (pc B A)

@[expose] noncomputable def keyP (i A B : Nat) : Nat :=
  Nat.add (Nat.mul (wconj i A) (Nat.pow 2 (4060 * 12))) (wconj i B)

@[expose] noncomputable def keyPL (f g : Nat → Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft ih 24) (Nat.lor (Nat.shiftLeft (f x) 12) (g x))) l

@[expose] noncomputable def ptsPQ : List Nat := [0, 1, 2, 3, 1000, 2022, 3000, 4059]

@[expose] noncomputable def keyPQ (i A B : Nat) (l : List Nat) : Nat :=
  keyPL (fun x => pg 12 (mask 12) (WS i) (pg 12 (mask 12) A (pg 12 (mask 12) (WSI i) x)))
    (fun x => pg 12 (mask 12) (WS i) (pg 12 (mask 12) B (pg 12 (mask 12) (WSI i) x))) l

@[expose] noncomputable def pairOK (j : Nat) : Bool :=
  strictB (bigP (Nat.add 7 (Nat.div j 15))) (fun A => strictB (bigP (Nat.mod j 15)) (fun B =>
    !pairCondK A B || Nat.ble 9 (distNL ((List.range 24).map fun i => keyPQ i A B ptsPQ)) ||
      Nat.ble 9 (distNL ((List.range 24).map fun i => keyP i A B))))

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.PRC CertificateChecks.KernelSporSch.RuB1K.pairOK 120

end
