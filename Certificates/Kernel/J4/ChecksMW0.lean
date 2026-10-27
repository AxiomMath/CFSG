module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem mw0 : Nat.beq (runM md kd MW0 (mkC (nat_lit 0) (nat_lit 1))) (nat_lit 8589934992) = true := by quickRfl

theorem mw1 : Nat.beq (runM md kd MW1 (nat_lit 8589934992)) (nat_lit 12884902688) = true := by quickRfl

theorem mw2 : Nat.beq (runM md kd MW2 (nat_lit 12884902688)) (nat_lit 12884903088) = true := by quickRfl

theorem mw3 : Nat.beq (runM md kd MW3 (nat_lit 12884903088)) (nat_lit 17179870784) = true := by quickRfl

theorem mw4 : Nat.beq (runM md kd MW4 (nat_lit 17179870784)) (nat_lit 17179871184) = true := by quickRfl

theorem mw5 : Nat.beq (runM md kd MW5 (nat_lit 17179871184)) (nat_lit 17179871584) = true := by quickRfl

theorem mw6 : Nat.beq (runM md kd MW6 (nat_lit 17179871584)) (nat_lit 17179871984) = true := by quickRfl

theorem mw7 : Nat.beq (runM md kd MW7 (nat_lit 17179871984)) (nat_lit 17179872384) = true := by quickRfl

theorem mw8 : Nat.beq (runM md kd MW8 (nat_lit 17179872384)) (nat_lit 21474840080) = true := by quickRfl

theorem mw9 : Nat.beq (runM md kd MW9 (nat_lit 21474840080)) (nat_lit 25769807776) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
