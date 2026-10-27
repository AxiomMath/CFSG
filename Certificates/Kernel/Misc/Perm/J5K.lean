module

public import Certificates.Kernel.Misc.Perm.J5B

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def GR (k : ℕ) : ℕ := nIf(Nat.beq k (nat_lit 2), JU.F 0, JS.F k)

@[expose] noncomputable def cm (p q : ℕ) : ℕ := CFSG.KC.Enum.pcomp 315 9 (mask 9) p q

@[expose] noncomputable def pw (p e : ℕ) : ℕ :=
  CFSG.KS.ppow 315 9 (mask 9) (CFSG.KC.Enum.pidn 315 9) p e

@[expose] noncomputable def relsK (BP X nb : ℕ) (rels : List (ℕ × ℕ × ℕ)) : Bool :=
  rels.all fun r => Nat.blt r.2.2 5 && Nat.blt r.1 nb && Nat.blt r.2.1 nb &&
    Nat.beq (pg 9 (mask 9) (pw X r.2.2) (pg 9 (mask 9) BP r.1)) (pg 9 (mask 9) BP r.2.1)

end CertificateChecks.KernelMisc.J2F

end
