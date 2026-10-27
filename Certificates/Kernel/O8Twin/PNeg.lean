module

public import Certificates.Kernel.O8Twin.PPairs
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P CFSG.KC.S7TwinK

theorem kN : Nat.beq (ordK ST.LR 5) 4096 = true := by decide +kernel

theorem neg_order : Nat.beq (ordK ST.LR 5) 2048 = false := by decide +kernel

theorem neg_total : Nat.beq NS.CS.sum (RS.N + 1) = false := by decide +kernel

theorem neg_k0 : pq8Rel 120 7 X0 (pinv 120 7 X0) X0 (pinv 120 7 X0) = false := by decide +kernel

noncomputable def badY0 (P : Nat) : Bool :=
  bAnd(ordIs 120 7 (mask 7) (pidn 120 7) P (4 - 1),
    !pairsY 120 7 sp0K repsK (candsK.map fun _ => []) P)

theorem neg_pairs : Nat.beq (strictN (ST.LR 0) (fun R => enumFrom 120 7 (mask 7) (120 * 7) ST.LR
    ST.TR badY0 4 1 (pcomp 120 7 (mask 7) One120 (ST.TR (roff 120 (120 * 7) R))) 0)) 0 =
    false := by
  decide +kernel

end CertificateChecks.KernelO8Twin

end
