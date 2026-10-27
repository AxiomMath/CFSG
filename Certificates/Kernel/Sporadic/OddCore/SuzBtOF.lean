module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtOD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Data.Kernel.Spor.BTupN
public import Certificates.Kernel.Sporadic.OddCore.SuzMGF
public import Certificates.Data.Kernel.Spor.BTupO
public import Certificates.Data.Kernel.Spor.BTupI
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtOF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kPre : btPreK 1782 11 (mask 11) 3 2 SuzBtM1.B SuzBtM1O.C SuzBtM1O.PRE = true := by
  quickRfl

theorem kOc : btOcSlK 11 (mask 11) 3 33 (mask 33) 2 SuzBtM1.cnt SuzBtM1.B (SuzTwG 6) SuzBtM1.G
    SuzBtM1.K SuzBtM1.R SuzBtM1O.C SuzBtM1O.PRE SuzBtM1O.TG 0 1024 = true := by quickRfl

theorem kOn : Nat.beq (btCntN SuzBtM1.cnt (fun i => btTgIn (btTg SuzBtM1O.TG i))) 288 = true := by
  quickRfl

theorem kCjN : allN 2 (fun j => allN 8 (fun l => btCjK 11 (mask 11) 3 33 (mask 33) SuzBtM1.cnt
    SuzBtM1.K SuzBtM1.B (SuzBtM1O.C j) (SuzBtM1.G l))) = true := by quickRfl

theorem kWM : Bool.not (allN SuzBtM1.cnt (fun q => Bool.not (btMov 11 (mask 11) 3 (SuzTwG 6)
    SuzBtM1.B (btKey 33 (mask 33) SuzBtM1.K q)))) = true := by quickRfl

theorem kWL : allN SuzBtL1.cnt (fun p => Bool.not (btMov 11 (mask 11) 3 (SuzTwG 6) SuzBtL1.B
    (btKey 33 (mask 33) SuzBtL1.K p))) = true := by quickRfl

theorem kFx : Nat.beq (btCntN 1782 (fun x => Nat.beq (pg 11 (mask 11) (SuzTwG 6) x) x)) 42 =
    true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtOF

end
