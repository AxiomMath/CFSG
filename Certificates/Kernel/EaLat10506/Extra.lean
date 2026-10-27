module

public import Certificates.Kernel.EaLat10506.Data

public section

namespace CertificateChecks.KernelEaLat10506

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

@[expose] noncomputable def tagMask (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e acc => Nat.lor acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) (TG e)) (Nat.blt (TG e) (nat_lit 191)))) m

@[expose] noncomputable def ch10506x : Bool := allN 4 fun j => bit (fixK (GT j)) 3

theorem ch10506t_ok : tagMask 1024 = 2 ^ 191 - 1 := by decide +kernel

theorem ch10506x_ok : ch10506x = true := by decide +kernel

end CertificateChecks.KernelEaLat10506

end
