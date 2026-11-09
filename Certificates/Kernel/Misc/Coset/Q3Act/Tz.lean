module

public import Certificates.Kernel.Misc.Coset.Q3Act.Rels
public import CFSG.Certificates.Kernel.Misc.Coset.PGTietze

public section

namespace CFSG.KAct.Q3

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

@[expose] def tzGen (X : List (List (ℕ × Bool))) (j : Fin nG) : List (Fin 12 × Bool) :=
  if j.val < 11 then [(Fin.ofNat 12 j.val, true)]
  else if j.val = 21 then [(11, true)]
  else (X.getD (repIdx3.getD (j.val - 11) 0) []).map fun l => (Fin.ofNat 12 l.1, l.2)

@[expose] def tzEmb (i : Fin 12) : Fin nG := Fin.ofNat nG (if i.val < 11 then i.val else 21)

theorem subCheck_rels :
    subCheck (tzGen CFSG.KD.OrdFi24p.rels) tzEmb (wsQN CFSG.KD.OrdFi24p.rels) = true := by
  decide +kernel

theorem subsetOf_emb : ∀ i ∈ subsetOf 12 S0, tzEmb i ∈ subsetOf nG S0 := by
  decide +kernel

theorem genSub_index_tz12 {N : ℕ}
    (h : (genSub (pgRels (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)))
        (subsetOf 12 S0)).FiniteIndex ∧
      (genSub (pgRels (tzRels (tzGen CFSG.KD.OrdFi24p.rels) (wsQN CFSG.KD.OrdFi24p.rels)))
        (subsetOf 12 S0)).index ≤ N) :
    (genSub (pgRels (wsQN CFSG.KD.OrdFi24p.rels)) (subsetOf nG S0)).FiniteIndex ∧
      (genSub (pgRels (wsQN CFSG.KD.OrdFi24p.rels)) (subsetOf nG S0)).index ≤ N :=
  genSub_index_tz (subOK_of_check subCheck_rels) subsetOf_emb h

end CFSG.KAct.Q3
