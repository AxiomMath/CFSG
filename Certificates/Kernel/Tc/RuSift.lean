module

public import Certificates.Kernel.Tc.RuHex
public import Certificates.Kernel.SporSch.Ru.JChain
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSporSch

@[expose] noncomputable def ok3 (k : Nat) : Bool :=
  bAnd(permOK 4060 12 (mask 12) (4060 * 12) (R3.F k) (I3 k),
    allN 4060 (fun i => Nat.blt (pg 12 (mask 12) (R3.F k) i) 4060))

@[expose] noncomputable def okT (k : Nat) : Bool :=
  bAnd(permOK 4060 12 (mask 12) (4060 * 12) (RT.F k) (IT k),
    allN 4060 (fun i => Nat.blt (pg 12 (mask 12) (RT.F k) i) 4060))

@[expose] noncomputable def siftJ (G : Nat) : Bool :=
  siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0 G

theorem kOk3 : allN 3 ok3 = true := by quickRfl

theorem kOkT : allN 13 okT = true := by quickRfl

theorem kSift3 : allN 3 (fun k => siftJ (R3.F k)) = true := by quickRfl

theorem kSiftT : allN 13 (fun k => siftJ (RT.F k)) = true := by quickRfl

end CertificateChecks.KernelTc.Ru

end
