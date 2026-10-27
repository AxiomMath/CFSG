module

public import Certificates.Kernel.SporSch.Ru.B1W
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def g2 (T0 T1 x : Nat) : Nat :=
  pg 12 (mask 12) T0 (pg 12 (mask 12) T1 x)

@[expose] noncomputable def sqFix (T0 T1 x : Nat) : Bool :=
  strictB (g2 T0 T1 x) (fun y => bIf(Nat.blt y 4060, Nat.beq (g2 T0 T1 y) x, true))

@[expose] noncomputable def sqPts : List Nat := [2022, 4059]

@[expose] noncomputable def keyPts : List Nat := [0]

@[expose] noncomputable def sqAll (T0 T1 : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(sqFix T0 T1 x, ih)) l

@[expose] noncomputable def keyC (T0 T1 i : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft ih 12)
      (pg 12 (mask 12) (WS i) (g2 T0 T1 (pg 12 (mask 12) (WSI i) x)))) l

@[expose] noncomputable def e8pF (T0 T1 : Nat) : Bool :=
  bIf(sqAll T0 T1 sqPts,
    bIf(Nat.ble 9 (distNL ((List.range 24).map fun i => keyC T0 T1 i keyPts)), true,
      e8pK (pcomp 4060 12 (mask 12) T0 T1)),
    true)

@[expose] noncomputable def e8rowF (a : Nat) : Bool :=
  strictB (RuS4.LR (nat_lit 0)) (fun R0 => strictB (RuS4.LR (nat_lit 1)) (fun R1 =>
  strictB (RuS4.TR (Nat.add (roff 4060 (4060 * 12) R0) a)) (fun T0 =>
  strictB (roff 4060 (4060 * 12) R1) (fun o1 =>
    allN (rcnt R1) (fun b => strictB (RuS4.TR (Nat.add o1 b)) (fun T1 => e8pF T0 T1))))))

end CertificateChecks.KernelSporSch.RuB1K

end
