module

public import Certificates.Kernel.EaLat318002.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelEaLat318002

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def tgMask (T : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (T e))) m

@[expose] noncomputable def tgW (T : Nat → Nat) : Bool :=
  letB (Nat.sub (Nat.pow (nat_lit 2) (nat_lit 191)) (nat_lit 1)) fun k =>
    Nat.beq (Nat.land (tgMask T (nat_lit 1024)) k) k

theorem ch318002t : tgW TG = true := by quickRfl

end CertificateChecks.KernelEaLat318002

end
