module

public import Certificates.Kernel.E27Spor.MOrbData
public import Certificates.Data.Kernel.E27Spor.SlpRec
public import Certificates.Data.Kernel.Spor.Row
public import CFSG.HardMathSupport.Foote.E27.SporMData

public section

namespace CertificateChecks.KernelE27Spor.MOrb

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.E27Spor CFSG.KS.Row CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Foote.E27

@[expose] noncomputable def tb (o i : Nat) : Nat := rg (nat_lit 32) (nat_lit 4294967295) TM o i

@[expose] noncomputable def RR (i : Nat) : Nat := tb (nat_lit 0) i

@[expose] noncomputable def AA (k : Nat) : Nat := tb (nat_lit 69) k

@[expose] noncomputable def BB (k : Nat) : Nat := tb (nat_lit 75) k

@[expose] noncomputable def OO (i : Nat) : Nat := tb (nat_lit 81) i

@[expose] noncomputable def C (i : Nat) : Nat := tb (nat_lit 82) i

@[expose] noncomputable def pp (i : Nat) : Nat := tb (nat_lit 151) i

@[expose] noncomputable def pj (i : Nat) : Nat := tb (nat_lit 220) i

@[expose] noncomputable def im (t i : Nat) : Nat :=
  tb (Nat.add (nat_lit 289) (Nat.mul (nat_lit 69) t)) i

@[expose] noncomputable def sg (q : Nat) : Nat := tb (nat_lit 496) q

@[expose] def base : List (List (List ℕ)) := [MAct.XRows, MAct.YRows, MAct.XiRows, MAct.YiRows]

@[expose] noncomputable def hrows : List (List (List ℕ)) :=
  [rowsR (nat_lit 12) RR (OO (nat_lit 0)), rowsR (nat_lit 12) RR (OO (nat_lit 1)),
    rowsR (nat_lit 12) RR (OO (nat_lit 2))]

@[expose] noncomputable def ch131302slp (q : Nat) : Bool :=
  blkC (nat_lit 8) (nat_lit 184) (slpAt (nat_lit 12) base (nat_lit 4) RR AA BB) q

@[expose] noncomputable def ch131302orb (q : Nat) : Bool :=
  blkC (nat_lit 27) (nat_lit 2187) (fun i => bAnd(orbTreeC (nat_lit 12) hrows C pp pj
    (lcode MAct.base) i, bAnd(orbImgC (nat_lit 12) hrows C im (nat_lit 2187) i,
      sortC C sg (nat_lit 2187) i))) q

end CertificateChecks.KernelE27Spor.MOrb

end
