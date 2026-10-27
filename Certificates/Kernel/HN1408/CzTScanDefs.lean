module

public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408.CzT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def czScan (T0 T1 : Nat → Nat) (F : Nat → Nat → Bool) : Bool :=
  allN 1280 fun i => strictB (T0 i) fun A => allN 24 fun j => F A (T1 j)

@[expose] noncomputable def commB (A B H g0 g1 : Nat) : Bool :=
  bAnd(Nat.beq (pt A (pt B (pt H 0))) (pt H g0), Nat.beq (pt A (pt B (pt H 1))) (pt H g1))

@[expose] noncomputable def isBase (g0 g1 v0 v1 : Nat) : Bool :=
  bAnd(Nat.beq g0 v0, Nat.beq g1 v1)

@[expose] noncomputable def ctRow (H0 H1 H2 a0 a1 z0 z1 c0 c1 A B : Nat) : Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    bIf(bAnd(commB A B H0 g0 g1, bAnd(commB A B H1 g0 g1, commB A B H2 g0 g1)),
      bIf(isBase g0 g1 0 1, true, bIf(isBase g0 g1 a0 a1, true,
        bIf(isBase g0 g1 z0 z1, true, isBase g0 g1 c0 c1))),
      true)

@[expose] noncomputable def ctK (T0 T1 : Nat → Nat) (H0 H1 H2 Ha Hz : Nat) : Bool :=
  strictB H0 fun H0 => strictB H1 fun H1 => strictB H2 fun H2 => strictB Ha fun Ha =>
    strictB Hz fun Hz => strictB (pc Ha Hz) fun Hc =>
      strictB (pt Ha 0) fun a0 => strictB (pt Ha 1) fun a1 => strictB (pt Hz 0) fun z0 =>
        strictB (pt Hz 1) fun z1 => strictB (pt Hc 0) fun c0 => strictB (pt Hc 1) fun c1 =>
          bAnd(commP H0 Hz, bAnd(commP H1 Hz, bAnd(commP H2 Hz, bAnd(commP Ha Hz,
            czScan T0 T1 (ctRow H0 H1 H2 a0 a1 z0 z1 c0 c1)))))

end CFSG.KD.HN1408.CzT

end
