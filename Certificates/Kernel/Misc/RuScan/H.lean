module

public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactC31RuData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.RuInv CertificateChecks.KernelSporSch
  CFSG.Quasithin.KGC31.Ru

@[expose] noncomputable def ch7230h_ (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 RuG.A0 RuG.A1) (gen2 RuG.A0I RuG.A1I) 2
    ((hWordsZ ++ hWordsA).getD i []) (HP (Nat.succ i))

theorem ch7230hz : Nat.beq (HP 0) RuG.Z = true := by quickRfl

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230h_ 0 9

end
