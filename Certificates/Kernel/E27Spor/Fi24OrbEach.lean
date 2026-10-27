module

public import Certificates.Kernel.E27Spor.Fi24OrbData
public import Certificates.Data.Kernel.E27Spor.OrbRec
public import Certificates.Data.Kernel.Spor.Row
public import CFSG.HardMathSupport.Foote.E27.SporFi24Data

public section

namespace CertificateChecks.KernelE27Spor.Fi24Orb

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.E27Spor CFSG.KS.Row CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Foote.E27

@[expose] noncomputable def tb (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) TF o i

@[expose] noncomputable def C (i : Nat) : Nat := tb (nat_lit 0) i

@[expose] noncomputable def pp (i : Nat) : Nat := tb (nat_lit 396) i

@[expose] noncomputable def pj (i : Nat) : Nat := tb (nat_lit 792) i

@[expose] noncomputable def im (t i : Nat) : Nat :=
  tb (Nat.add (nat_lit 1188) (Nat.mul (nat_lit 396) t)) i

@[expose] noncomputable def sg (q : Nat) : Nat := tb (nat_lit 1980) q

@[expose] def rows : List (List (List ℕ)) := [Fi24.XRows, Fi24.YRows]

@[expose] noncomputable def ch131300orb (q : Nat) : Bool :=
  blkC (nat_lit 64) (nat_lit 12672) (fun i => bAnd(orbTreeC (nat_lit 10) rows C pp pj
    (lcode Fi24.base) i, bAnd(orbImgC (nat_lit 10) rows C im (nat_lit 12672) i,
      sortC C sg (nat_lit 12672) i))) q

end CertificateChecks.KernelE27Spor.Fi24Orb

end
