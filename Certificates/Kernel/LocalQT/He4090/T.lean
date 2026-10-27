module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeWitInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWitCheck

public section

namespace CFSG.KD.LQT.H4090

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.HePairs CFSG.QuasithinUnique.K1.SporadicPerm

def rijs : List (Nat × Nat) := [(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

def cpT : Array (Array Nat) :=
  let r1 := quotGt 8330 heL2 r2a
  let r2 := quotGt 8330 heL2 r2b
  let xs := rijs.map fun p => rijTab 8330 r1 r2 p.1 p.2
  #[idTab 8330, heL2[4]!, wordTabA #[heTa, heTb] 8330 (((heMwLit[7]!)[0]!).drop 12), heL7[4]!,
      r1, r2] ++ (q2s.map (quotGt 8330 heL2)).toArray ++ (q2s.map (quotGi 8330 heL2)).toArray ++
    xs.toArray ++ (xs.map fun x => powTab 8330 x 2).toArray ++
    #[quotGt 8330 heL7 b7a, quotGi 8330 heL7 b7a, quotGt 8330 heL7 q7a, quotGi 8330 heL7 q7a,
      quotGt 8330 heL7 q7b, quotGi 8330 heL7 q7b, quotGt 8330 heL7 b7p, commOf 8330 heL7 q7a b7a,
      commOf 8330 heL7 q7b b7a]

def cpQp : List (Nat × Nat) := []

end CFSG.KD.LQT.H4090

end
