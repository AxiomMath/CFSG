module

public import Certificates.Kernel.HeLoc.Seven0Chain
public import Certificates.Kernel.HeLoc.MemDefs
public import Certificates.Kernel.Sporadic.He.Chain2112
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

theorem k0Bind : allN 10 (fun j => Nat.beq (S70T.F j) (S70.S j)) = true := by quickRfl

theorem k0Perm : allN 10 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (S70.S j) (S70.SI j)) =
    true := by quickRfl

theorem k0Gen : bAnd(Nat.beq (S70.S 0) (HeC.S 0), Nat.beq (S70.S 1) (HeC.S 1)) = true := by
  quickRfl

@[expose] noncomputable def u0B (c : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 833 c) 833 fun x =>
    bIf(Nat.blt x 8330, Nat.beq (pg 14 (mask 14) (S70.S 2) x) (uM x), true)

theorem k0U : allN 10 u0B = true := by quickRfl

theorem k0Base : allN 14 (fun t => Nat.beq CFSG.RankThree.PartOne.heSevenCase0BaseArr[t]!
    (pg 14 (mask 14) S70.BP t)) = true := by quickRfl

theorem k0Prod : Nat.beq (((List.range 14).map fun i => rcnt (S70.LR i)).prod) 8060774400 =
    true := by quickRfl

end CertificateChecks.KernelHeLoc.Seven

end
