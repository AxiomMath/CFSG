module

public import Certificates.Kernel.EaLat318002.Data
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 NC
  "Certificates/Kernel/EaLat318002/data/nc.bin" 16 4 9472 14795898062538787614
#kc_repo #kc_ktree CertificateChecks.KernelEaLat318002 PG
  "Certificates/Kernel/EaLat318002/data/pg.bin" 4 4 2360 7041589537698755005

public section

namespace CertificateChecks.KernelEaLat318002

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

set_option maxRecDepth 100000

@[expose] noncomputable def slpW (N : Nat → Nat) (k : Nat) : Bool :=
  letB (PG k) fun r => letB (fld r (nat_lit 0) (nat_lit 65535)) fun a =>
    letB (fld r (nat_lit 16) (nat_lit 65535)) fun b =>
      andB (Nat.blt a (Nat.add k (nat_lit 2))) (andB (Nat.blt b (Nat.add k (nat_lit 2)))
        (Nat.beq (N (Nat.add k (nat_lit 2))) (mul (nat_lit 24) (N a) (N b))))

@[expose] noncomputable def slpAt (k : Nat) : Bool := slpW NC k

@[expose] noncomputable def ch318002s (k : Nat) : Bool :=
  allN (nat_lit 20) fun d => letB (Nat.add (Nat.mul (nat_lit 20) k) d) fun s =>
    impB (Nat.blt s (nat_lit 590)) (slpAt s)

#kc_each ch318002s 0 30

theorem ch318002s_ab : andB (Nat.beq (NC (nat_lit 0)) 817395973838868159142633316802379971)
    (Nat.beq (NC (nat_lit 1)) 938078705133617800621527216201835139) = true := by quickRfl

theorem ch318002s_gr : andB (Nat.beq (GR (nat_lit 0)) (NC (nat_lit 161)))
    (andB (Nat.beq (GR (nat_lit 1)) (NC (nat_lit 303)))
      (andB (Nat.beq (GR (nat_lit 2)) (NC (nat_lit 431)))
        (Nat.beq (GR (nat_lit 3)) (NC (nat_lit 591))))) = true := by quickRfl

@[expose] noncomputable def ncBad (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (NC k) (Nat.xor (NC k) (nat_lit 1)) (Nat.beq k (nat_lit 100))

theorem ch318002n_slp : notB (slpW ncBad (nat_lit 98)) = true := by quickRfl

end CertificateChecks.KernelEaLat318002

end
