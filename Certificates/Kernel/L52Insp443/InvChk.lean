module

public import Certificates.Kernel.L52Insp443.OrbData
public import Certificates.Data.L52Insp443
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th.Native

@[expose] noncomputable def ch725108one (c : Nat) : Bool :=
  andB (invoK c) (andB (orbOneK (O.px.getD 0 []) (O.qx.getD 0 []) (O.cs.getD 0 []) c)
    (andB (orbOneK (O.px.getD 1 []) (O.qx.getD 1 []) (O.cs.getD 1 []) c)
      (orbOneK (O.px.getD 2 []) (O.qx.getD 2 []) (O.cs.getD 2 []) c)))

@[expose] noncomputable def ch725108i (k : Nat) : Bool :=
  andB (ascK (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j _ => lastK (nat_lit 0) (O.inv.getD j [])) k) (O.inv.getD k []))
    (allK ch725108one (O.inv.getD k []))

@[expose] noncomputable def ch725108n (_ : Nat) : Bool :=
  Nat.beq (List.foldr (fun L acc => Nat.add (List.length L) acc) (nat_lit 0) O.inv) (nat_lit 6975)

@[expose] def ch725108pt : List (Nat × Table) := [(5, x5T), (7, x7T), (31, x31T)]

@[expose] noncomputable def ch725108x (i : Nat) : Bool :=
  letL (O.px.getD i []) fun ps => letL (O.qx.getD i []) fun qs =>
  letB (ch725108pt.getD i (0, #[])).1 fun p =>
    andB (Nat.beq (ps.getD 0 0) idK)
    (andB (allK (fun j => Nat.beq (mmulK (ps.getD j 0) (ps.getD 1 0)) (ps.getD (j + 1) 0))
      (List.range (Nat.sub p 1)))
    (andB (Nat.beq (List.length ps) p) (andB (Nat.beq (List.length qs) p)
    (andB (allK (fun j => andB (Nat.beq (mmulK (ps.getD j 0) (qs.getD j 0)) idK)
      (unitK (qs.getD j 0))) (List.range p))
    (andB (ordK (ps.getD 1 0) p)
      (andB (unitK (ps.getD 1 0)) (tabK (ps.getD 1 0) (ch725108pt.getD i (0, #[])).2)))))))

@[expose] noncomputable def ch725108t (i : Nat) : Bool :=
  letL ([cands5, cands7].getD i []) fun Ts =>
    andB (Nat.beq (List.length (O.cs.getD i [])) (List.length Ts))
      (allK (fun j => tabsK ((O.cs.getD i []).getD j []) (Ts.getD j [])) (List.range (List.length Ts)))

#kc_each ch725108x 0 3
#kc_each ch725108t 0 2
#kc_each ch725108n 0 1
#kc_each ch725108i 0 28

end CertificateChecks.KernelL52I

end
