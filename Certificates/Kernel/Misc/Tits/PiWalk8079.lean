module

public import Certificates.Data.Kernel.SporSch.TitsEnum5
public import Certificates.Kernel.Sporadic.Tits.LocS
public import Certificates.Kernel.Misc.Tits.Pi7092
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsPW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSpor

@[expose] noncomputable def commQ (Q G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i =>
    Nat.beq (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) Q (pg 11 (mask 11) G i)))
      (pg 11 (mask 11) G (gpt 11 (mask 11) t0 t1 t2 t3 t4 (pg 11 (mask 11) Q i))))

@[expose] noncomputable def ncQ (Q t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(allN 3 (fun j => commQ Q (TitsS.S j) t0 t1 t2 t3 t4), false, true)

theorem walk : all5K 1755 (1755 * 11) TitsS.LR TitsS.TR
    (fun _ => ncQ CertificateChecks.KernelMisc.TitsPi.P) = true := by quickRfl

end CertificateChecks.KernelMisc.TitsPW

end
