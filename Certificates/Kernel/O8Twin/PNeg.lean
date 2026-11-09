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

noncomputable def pairsZ0 (Y : Nat) : Bool :=
  strictB (pc 120 7 Y Y) (fun Y2 =>
    allE 120 7 SP CA CB Y Y2 (pc 120 7 Y2 Y) RA RB RC (perRepO.map fun _ => []) RE)

theorem neg_pairs : allN 53 (fun i => pairsZ0 (RS.E i)) = false := by decide +kernel

end CertificateChecks.KernelO8Twin

end
