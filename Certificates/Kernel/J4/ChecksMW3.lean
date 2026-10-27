module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem mw30 : Nat.beq (runM md kd MW30 (nat_lit 330712493792)) (nat_lit 347892363376) = true := by quickRfl

theorem mw31 : Nat.beq (runM md kd MW31 (nat_lit 347892363376)) (nat_lit 373662167552) = true := by quickRfl

theorem mw32 : Nat.beq (runM md kd MW32 (nat_lit 373662167552)) (nat_lit 390842037136) = true := by quickRfl

theorem mw33 : Nat.beq (runM md kd MW33 (nat_lit 390842037136)) (nat_lit 412316874016) = true := by quickRfl

theorem mw34 : Nat.beq (runM md kd MW34 (nat_lit 412316874016)) (nat_lit 433791710896) = true := by quickRfl

theorem mw35 : Nat.beq (runM md kd MW35 (nat_lit 433791710896)) (nat_lit 468151449664) = true := by quickRfl

theorem mw36 : Nat.beq (runM md kd MW36 (nat_lit 468151449664)) (nat_lit 493921253840) = true := by quickRfl

theorem mw37 : Nat.beq (runM md kd MW37 (nat_lit 493921253840)) (nat_lit 528280992608) = true := by quickRfl

theorem mw38 : Nat.beq (runM md kd MW38 (nat_lit 528280992608)) (nat_lit 558345764080) = true := by quickRfl

theorem mw39 : Nat.beq (runM md kd MW39 (nat_lit 558345764080)) (nat_lit 605590404736) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
