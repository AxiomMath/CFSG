module

public import Certificates.Kernel.SporSch.Tits.Inv2266D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def P2 (t0 t1 t2 t3 t4 : Nat) : Bool :=
  bIf(Nat.beq (gpt 11 (mask 11) t0 t1 t2 t3 t4 (gpt 11 (mask 11) t0 t1 t2 t3 t4 (nat_lit 1754)))
      (nat_lit 1754),
    bIf(memPts 1755 11 (mask 11) TitsIC t0 t1 t2 t3 t4, true,
      bIf(sqPts 1755 11 (mask 11) t0 t1 t2 t3 t4,
        bIf(eqPts 1755 11 (mask 11) (pidn 1755 11) t0 t1 t2 t3 t4, true, false), true)),
    true)

@[expose] noncomputable def Q2 : Nat → Nat → Nat → Nat → Nat → Nat → Bool := fun _ => P2

#kst_all5 CertificateChecks.KernelSporSch.TitsS2 1755 11 8 2 TitsS.LR TitsS.TR Q2

end CertificateChecks.KernelSporSch.TitsInv

end
