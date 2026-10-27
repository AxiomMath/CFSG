module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def d4W : List (List Int) := [[1], [5], [7], i1021HighRootWord]

@[expose] noncomputable def d4K (i : Nat) : Nat := wO (d4W.getD i [])

@[expose] noncomputable def d4Prod (e0 e1 e2 e3 : Nat) : Nat :=
  pc (ppw (d4K 0) e0) (pc (ppw (d4K 1) e1) (pc (ppw (d4K 2) e2) (pc (ppw (d4K 3) e3) pid)))

theorem kD4 : bAnd(allN 4 (fun i => bAnd(lettersK 17 (d4W.getD i []), bAnd(cn (d4K i),
    bAnd(cn (ppw (d4K i) 0), bAnd(cn (ppw (d4K i) 1), bAnd(Nat.beq (pc (d4K i) (d4K i)) pid,
      allN 4 fun j => Nat.beq (pc (d4K i) (d4K j)) (pc (d4K j) (d4K i)))))))),
    allN 2 fun e0 => allN 2 fun e1 => allN 2 fun e2 => allN 2 fun e3 =>
      bIf(Nat.beq (Nat.add (Nat.add e0 e1) (Nat.add e2 e3)) 0, true,
        bIf(Nat.beq (d4Prod e0 e1 e2 e3) pid, false, true))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
