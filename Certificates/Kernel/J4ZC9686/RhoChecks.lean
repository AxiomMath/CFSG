module

public import Certificates.Kernel.J4ZC9686.RhoData
public import Certificates.Data.Kernel.J4ZC9686Rho
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4ZC9686

open CFSG.KC.J4ZC9686 CFSG.KC.J4M2K CFSG.KS.PK CFSG.Quasithin.J4M2 CFSG.KC.Enum
open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat (p5Gens)
open CFSG.Sporadic.J4.ZCent (rW tW)

@[expose] noncomputable def ch9686phiL (j : Nat) : Bool :=
  strictB hexP fun H => strictB (gimg (p5Gens.getD j 1)) fun G =>
    allR (nat_lit 77) fun i => Nat.beq (phiK H (fd (nat_lit 5) G) i) ((PL.getD j []).getD i 0)

#kc_each ch9686phiL 0 2

@[expose] noncomputable def ch9686perm (j : Nat) : Bool :=
  (List.range 77).all fun i =>
    ((permImg (PL.getD j [])) (Fin.ofNat 77 i)).val == (PL.getD j []).getD i 0

#kc_each ch9686perm 0 2

theorem ch9686neg : (rW.all negOK && tW.all negOK) = true := by decide

theorem ch9686rho : rhoChk (PL.getD 0 []) (PL.getD 1 []) = true := by quickRfl

@[expose] noncomputable def notR (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

theorem ch9686neg_rho : notR (rhoChk (PL.getD 1 []) (PL.getD 0 [])) = true := by
  quickRfl

theorem ch9686neg_phiL : notR (strictB hexP fun H =>
    strictB (gimg (p5Gens.getD 1 1)) fun G =>
      allR (nat_lit 77) fun i => Nat.beq (phiK H (fd (nat_lit 5) G) i) ((PL.getD 0 []).getD i 0)) =
    true := by quickRfl

end CertificateChecks.KernelJ4ZC9686
