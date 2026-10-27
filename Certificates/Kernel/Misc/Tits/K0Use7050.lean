
module

public import Certificates.Kernel.Misc.Tits.Cls7050D
public import Certificates.Kernel.Misc.Tits.K0D7050

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Tits7050

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem kS : allN 5 (fun j => Nat.beq (TitsK0.S j) (TK.F j)) = true := by decide +kernel

theorem kB : allN 3 (fun t => Nat.beq (pg 11 (mask 11) TitsK0.BP t)
    (CFSG.KS.Mathieu.nget [0, 12, 1] t)) = true := by decide +kernel

theorem good : allN 30 (fun i => bIf(CFSG.Quasithin.RuRank3.titsRepGood.getD i false,
    siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK0.LR TitsK0.TRI TitsK0.BP 3 0 (R i),
    true)) = true := by decide +kernel

end CertificateChecks.KernelMisc.Tits7050

end
