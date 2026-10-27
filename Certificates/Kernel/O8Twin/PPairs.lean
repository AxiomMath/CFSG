module

public import Certificates.Kernel.O8Twin.PChecks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P

@[expose] noncomputable def badK (k : Nat) : Bool :=
  strictB (ST.LR (nat_lit 0)) (fun R => bIf(Nat.blt k (rcnt R),
    Nat.beq (enumFrom 120 7 (mask 7) (120 * 7) ST.LR ST.TR badY (nat_lit 4) (nat_lit 1)
      (pcomp 120 7 (mask 7) One120 (ST.TR (Nat.add (roff 120 (120 * 7) R) k))) (nat_lit 0))
      (nat_lit 0), true))

theorem ch517202o : Nat.ble (rcnt (ST.LR 0)) 64 = true := by decide +kernel

end CertificateChecks.KernelO8Twin

#kc_each CertificateChecks.KernelO8Twin.badK 0 64

end
