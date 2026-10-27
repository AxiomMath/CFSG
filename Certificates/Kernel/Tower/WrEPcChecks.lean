module

public import Certificates.Kernel.Tower.WrEChecks
public import Certificates.Data.Kernel.Tower.PcP
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def ch36408_epcP (e : Nat) : Bool :=
  pcP 16384 (wrEM e) (wrED e 0) (wrED e 1) (wrED e 2) (wrED e 3) (wrEP e 2) 128 (l16 (wrED e 5) 0)

#kc_each ch36408_epcP 0 12

#kc_forall_tree ch36408_epcP_all (fun e => ch36408_epcP e = true) 12
  Certificates.KernelTower.ch36408_epcP

theorem ch36408_e_pcP_neg : (!pcP 16384 (wrEM 0) (wrED 0 0) (wrED 0 1) (wrED 0 2) (wrED 0 3)
    (wrEP 0 2) 128 128) = true := by
  decide +kernel

end Certificates.KernelTower
