module

public import Certificates.Kernel.SporSch.Ru.C2248
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuB1K CertificateChecks.KernelSporSch.RuLines

@[expose] noncomputable def zjpK (G : Nat) : Bool :=
  bIf(allN 6 (fun j => cm G (RuT1920.L (Nat.add 24 j))),
    bIf(Nat.beq G (pidn 1920 11), true, Nat.beq G (RF 0)), true)

@[expose] noncomputable def zjRow (a : Nat) : Bool :=
  row2K 1920 11 (mask 11) (1920 * 11) RuJS2.LR RuJS2.TR zjpK a

theorem cJ0 : Nat.beq (rcnt (RuJS2.LR 0)) 128 = true := by quickRfl

theorem ch9680neg : (!bIf(allN 0 (fun k => cm (RuT1920.L 24) (RuT1920.L (Nat.add 24 k))),
    bIf(Nat.beq (RuT1920.L 24) (pidn 1920 11), true, Nat.beq (RuT1920.L 24) (RF 0)), true)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.RuCt

#kss_each CertificateChecks.KernelSporSch.RuCt.ZJ CertificateChecks.KernelSporSch.RuCt.zjRow 128

end
