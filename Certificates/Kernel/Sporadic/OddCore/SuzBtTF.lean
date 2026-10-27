module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtTD
public import Certificates.Data.Kernel.Spor.BTupI
public import Certificates.Data.Kernel.Spor.BTupO
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtTF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kT0Hd : btHdK SuzBtT0.cnt = true := by quickRfl

theorem kT0Cnt : SuzBtT0.cnt = 64 := by decide

theorem kT0Sl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtT0.cnt SuzBtT0.B SuzBtT0.G
    SuzBtT0.K SuzBtT0.R SuzBtT0.POS 0 64 = true := by quickRfl

theorem kT0S : allN 4 (fun j => btMov 11 (mask 11) 3 (SuzBtT0.G j) SuzBtT0.B
    (btKey 33 (mask 33) SuzBtT0.K (SuzBtT0Z.S j))) = true := by quickRfl

theorem kT0Rt : btRtSlK 4 4 SuzBtT0.cnt SuzBtT0Z.S SuzBtT0.R SuzBtT0.POS SuzBtT0Z.RT 0 64 =
    true := by quickRfl

theorem kT0I : Nat.beq (btCntN SuzBtT0.cnt (btInvP 4 33 (mask 33) 1 SuzBtT0.K SuzBtT0.R
    SuzBtT0Z.RT (fun _ => SuzBtT0.B))) 27 = true := by quickRfl

theorem kT0Fx : allN SuzBtT0.cnt (fun i => bIf(btInvP 4 33 (mask 33) 1 SuzBtT0.K SuzBtT0.R
    SuzBtT0Z.RT (fun _ => SuzBtT0.B) i,
    Nat.beq (btCntN 1782 (fun p => Nat.beq (btWalk 11 (mask 11) SuzBtT0.G SuzBtT0.R i p) p)) 54,
    true)) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtTF

end
