module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem mw10 : Nat.beq (runM md kd MW10 (nat_lit 25769807776)) (nat_lit 30064775472) = true := by quickRfl

theorem mw11 : Nat.beq (runM md kd MW11 (nat_lit 30064775472)) (nat_lit 38654710464) = true := by quickRfl

theorem mw12 : Nat.beq (runM md kd MW12 (nat_lit 38654710464)) (nat_lit 55834580048) = true := by quickRfl

theorem mw13 : Nat.beq (runM md kd MW13 (nat_lit 55834580048)) (nat_lit 68719482336) = true := by quickRfl

theorem mw14 : Nat.beq (runM md kd MW14 (nat_lit 68719482336)) (nat_lit 81604384624) = true := by quickRfl

theorem mw15 : Nat.beq (runM md kd MW15 (nat_lit 81604384624)) (nat_lit 103079221504) = true := by quickRfl

theorem mw16 : Nat.beq (runM md kd MW16 (nat_lit 103079221504)) (nat_lit 111669156496) = true := by quickRfl

theorem mw17 : Nat.beq (runM md kd MW17 (nat_lit 111669156496)) (nat_lit 128849026080) = true := by quickRfl

theorem mw18 : Nat.beq (runM md kd MW18 (nat_lit 128849026080)) (nat_lit 150323862960) = true := by quickRfl

theorem mw19 : Nat.beq (runM md kd MW19 (nat_lit 150323862960)) (nat_lit 163208765248) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
