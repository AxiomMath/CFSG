
module

public import Certificates.Kernel.SporSch.Ru.Rows7045D
public import Certificates.Kernel.SporSch.Ru.TreeData
public import Certificates.Kernel.SporSch.Ru.Q7307K
public import Certificates.Data.Kernel.SporSch.RowTreeK
public import Certificates.Data.Kernel.SporSch.RuTreeK
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Ru7045

open CFSG.KC.Enum CFSG.KS CFSG.KS.RowTree CFSG.KS.RuTree CFSG.KLC.Fi22 CertificateChecks.KernelSporSch

@[expose] noncomputable def Row (x : Nat) : Nat := Ru7045D.RW x

@[expose] noncomputable def parK (x : Nat) : Nat := pg 12 (mask 12) Iso7047.Par x

@[expose] noncomputable def labK (x : Nat) : Nat := pg 4 (mask 4) Iso7047.Lab x

@[expose] noncomputable def rowAt (x : Nat) : Bool :=
  rowK RuTD.NW0 RuTD.NW1 (nat_lit 4060) Row parK labK (nat_lit 32) x

@[expose] noncomputable def rows (c : Nat) : Bool :=
  rngK (Nat.mul (nat_lit 256) c) (nat_lit 256) (fun x =>
    orB (Nat.beq x (nat_lit 0)) (orB (notB (Nat.blt x (nat_lit 4060))) (rowAt x)))

end CertificateChecks.KernelSporSch.Ru7045

#kc_each CertificateChecks.KernelSporSch.Ru7045 ch7045row CertificateChecks.KernelSporSch.Ru7045.rows 0 16

namespace CertificateChecks.KernelSporSch.Ru7045

open CFSG.KC.Enum CFSG.KS CFSG.KS.RowTree CFSG.KS.RuTree CFSG.KLC.Fi22 CertificateChecks.KernelSporSch

@[expose] noncomputable def wIdx (i : Nat) : Nat :=
  List.getD [1648, 319, 495, 1445, 265, 189, 402, 552, 1115, 1710, 1612, 261, 1136, 907, 956, 1712,
    1628, 491, 326, 753] i (nat_lit 0)

@[expose] noncomputable def wPt (i : Nat) : Nat := pg 12 (mask 12) Iso7047.D (wIdx i)

@[expose] noncomputable def fp (x : Nat) : Nat := fpK Row wPt (nat_lit 20) x

@[expose] noncomputable def ent (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Ru7045D.FK (Nat.shiftRight i (nat_lit 6)))
    (Nat.mul (nat_lit 32) (Nat.land i (nat_lit 63)))) (maskN (nat_lit 32))

@[expose] noncomputable def Lk (i : Nat) : Nat := Nat.land (ent i) (nat_lit 65535)

@[expose] noncomputable def Pk (x : Nat) : Nat := Nat.shiftRight (ent x) (nat_lit 16)

@[expose] noncomputable def inS (x : Nat) : Bool := Nat.beq (Q7307.Lf x) (Q7307.Lf (nat_lit 2808))

theorem kRoot : rootK (nat_lit 4060) (Row (nat_lit 0)) Q7307.Lf (Q7307.Lf (nat_lit 1)) = true := by
  quickRfl

theorem kCover : allN 4060 (coverK inS Pk Lk (nat_lit 2304)) = true := by quickRfl

theorem kKeys : allN 2304 (keyK fp Lk (nat_lit 2304)) = true := by quickRfl

theorem neg : andB (notB (edgeK RuTD.NW0 RuTD.NW1 (nat_lit 4060) (Row (nat_lit 1)) (Row (parK (nat_lit 1)))
      (Nat.succ (Nat.mod (labK (nat_lit 1)) (nat_lit 4)))))
    (andB (notB (rootK (nat_lit 4060) (Nat.xor (Row (nat_lit 0)) (nat_lit 1)) Q7307.Lf
      (Q7307.Lf (nat_lit 1))))
    (andB (notB (keyK fp (fun i => Lk (Nat.sub (nat_lit 2303) i)) (nat_lit 2304) (nat_lit 0)))
      (notB (allN 4060 (coverK inS (fun x => Nat.succ (Pk x)) Lk (nat_lit 2304)))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Ru7045

end
