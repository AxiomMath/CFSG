module

public import Certificates.Kernel.RouteP.Data.Pres
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverInputs
public import CFSG.Certificates.Kernel.Orders.Fi24p.Rels

public section

namespace CFSG.KD.RouteP

open CFSG.KC CFSG.KC.RouteP CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

@[expose] def litI (l : Fin nG × Bool) : Int :=
  if l.2 then (l.1.val : Int) + 1 else -((l.1.val : Int) + 1)

@[expose] def cq (l : Int) : Int :=
  if l.natAbs ≤ 11 then (if 0 < l then -(l + 28) else -l + 28)
  else if l.natAbs = 22 then (if 0 < l then -42 else 42) else 0

@[expose] def litN (l : Nat × Bool) : Int :=
  if l.2 then ((l.1 % 22 : Nat) : Int) + 1 else -(((l.1 % 22 : Nat) : Int) + 1)

@[expose] def relsQ : List (List Int) :=
  (CFSG.KD.OrdFi24p.rels.filter fun w => !(w.any fun l => l.1 == 8)).map (·.map litN) ++
    [(CFSG.KD.OrdFi24p.rels.getD sqIdx []).map litN] ++
    (List.range 11).flatMap fun k =>
      [(CFSG.KD.OrdFi24p.rels.getD (repIdx3.getD k 0) []).map litN ++ [-((12 + k : Nat) : Int)],
        List.replicate 9 ((12 + k : Nat) : Int)] ++
      (List.range 11).map fun i =>
        [((12 + k : Nat) : Int), ((i + 1 : Nat) : Int), -((12 + k : Nat) : Int), -((i + 1 : Nat) : Int)]

@[expose] def qw (i : Nat) : List Int := (relsQ[i]!).map cq

@[expose] noncomputable def qck (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (idKOK NWP KAP KBP (qw (Nat.div g 20)))
    (idOK NWP (qw (Nat.div g 20)) (Nat.mod g 20)) (Nat.blt (Nat.mod g 20) 19)

@[expose] noncomputable def nkP (j : Nat) : Bool :=
  andB (CFSG.KC.Fi24Net.netOK (NWP j)) (kapOK KAP KBP j)

@[expose] noncomputable def zck (k : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.beq (KAP (nat_lit 41)) (MonsterConv.Perm.ones (nat_lit 306936))) (Nat.beq (KBP (nat_lit 41)) 0))
    (wordOK NWP [] (nat_lit 41) k) (Nat.blt k 19)

@[expose] noncomputable def transOK : Bool := orbOK NWP KAP KBP [-1, -2] 0 62 920808

@[expose] def zpL : List Int := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]

@[expose] noncomputable def zpOK : Bool := orbOK NWP KAP KBP zpL 1479 33 31671

end CFSG.KD.RouteP

end
