
module

public import Certificates.Kernel.SporSch.Ru.Rows7045K
public import Certificates.Kernel.SporSch.Tits.Graph2265K
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Ru7045

open CFSG.KC.Enum CFSG.KS CFSG.KS.RowTree CFSG.KS.RuTree CFSG.KLC.Fi22 CFSG.KS.SporSch
  CertificateChecks.KernelSporSch

@[expose] noncomputable def popK (r n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (bt r i)) n

@[expose] noncomputable def mS (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun y acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) y))
      (inS y)) n

@[expose] noncomputable def nbrK (k j : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun i acc => orB acc (Nat.beq (pgW 11 TitsGN.NB i) j)) k

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def dPt (j : Nat) : Nat := pg 12 (mask 12) Iso7047.D j

@[expose] noncomputable def cntAt (c M j : Nat) : Bool :=
  eqB (Nat.beq (popK (Nat.land M (Row (dPt j))) (nat_lit 4060)) c) (nbrK (nat_lit 10) j)

@[expose] noncomputable def cnt (c : Nat) : Bool :=
  sB (Nat.land (mS (nat_lit 4060)) (Row (nat_lit 1))) (fun M =>
    rngK (Nat.mul (nat_lit 110) c) (nat_lit 110) (fun j =>
      orB (notB (Nat.blt j (nat_lit 1755))) (cntAt (nat_lit 512) M j)))

end CertificateChecks.KernelSporSch.Ru7045

#kc_each CertificateChecks.KernelSporSch.Ru7045 ch7045cnt CertificateChecks.KernelSporSch.Ru7045.cnt 0 16

namespace CertificateChecks.KernelSporSch.Ru7045

open CFSG.KC.Enum CFSG.KS CFSG.KS.RowTree CFSG.KS.RuTree CFSG.KLC.Fi22 CFSG.KS.SporSch
  CertificateChecks.KernelSporSch

theorem negCnt : sB (Nat.land (mS (nat_lit 4060)) (Row (nat_lit 1))) (fun M =>
    andB (notB (cntAt (nat_lit 511) M (pgW 11 TitsGN.NB (nat_lit 0))))
      (notB (eqB (Nat.beq (popK (Nat.land M (Row (dPt (pgW 11 TitsGN.NB (nat_lit 9))))) (nat_lit 4060))
        (nat_lit 512)) (nbrK (nat_lit 9) (pgW 11 TitsGN.NB (nat_lit 9)))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Ru7045

end
