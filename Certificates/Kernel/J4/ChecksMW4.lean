module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

theorem mw40 : Nat.beq (runM md kd MW40 (nat_lit 605590404736)) (nat_lit 635655176208) = true := by quickRfl

theorem mw41 : Nat.beq (runM md kd MW41 (nat_lit 635655176208)) (nat_lit 665719947680) = true := by quickRfl

theorem mw42 : Nat.beq (runM md kd MW42 (nat_lit 665719947680)) (nat_lit 712964588336) = true := by quickRfl

theorem mw43 : Nat.beq (runM md kd MW43 (nat_lit 712964588336)) (nat_lit 764504196288) = true := by quickRfl

theorem mw44 : Nat.beq (runM md kd MW44 (nat_lit 764504196288)) (nat_lit 828928706128) = true := by quickRfl

theorem mw45 : Nat.beq (runM md kd MW45 (nat_lit 828928706128)) (nat_lit 927712954336) = true := by quickRfl

theorem mw46 : Nat.beq (runM md kd MW46 (nat_lit 927712954336)) (nat_lit 1125281450352) = true := by quickRfl

theorem mw47 : Nat.beq (runM md kd MW47 (nat_lit 1125281450352)) (nat_lit 1391569423104) = true := by quickRfl

theorem mw48 : Nat.beq (runM md kd MW48 (nat_lit 1391569423104)) (nat_lit 1709397003408) = true := by quickRfl

theorem mw49 : Nat.beq (runM md kd MW49 (nat_lit 1709397003408)) (mkC md.NF md.ND) = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
