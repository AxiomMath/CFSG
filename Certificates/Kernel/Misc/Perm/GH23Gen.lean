module

public meta import Certificates.Data.GH23Data
public meta import Certificates.Data.GH23Perm

public section

namespace CFSG.KC.Misc.GH23Gen

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

meta def gensL : List (List Nat) := members.map (·.gens) ++ [q2gens]

meta def elemsOf (gs : List Nat) : Array Nat := #[oneC] ++ ((bfsChain gs).map (·.1)).toArray

meta def indexOf (E : Array Nat) : Std.HashMap Nat Nat :=
  (List.range E.size).foldl (fun m t => m.insert E[t]! t) {}

meta def posOf (gs : List Nat) (g : Nat) : Nat := (gs.takeWhile (· != g)).length

meta def parOf (gs : List Nat) : List Nat :=
  let idx := indexOf (elemsOf gs)
  0 :: (bfsChain gs).map fun t => idx.getD t.2.1 0 + 2 ^ 24 * posOf gs t.2.2

meta def sortOf (E : Array Nat) : List Nat :=
  ((Array.range E.size).qsort fun a b => E[a]! < E[b]!).toList

meta def closOf (gs : List Nat) : List Nat :=
  let E := elemsOf gs
  let idx := indexOf E
  (List.range E.size).flatMap fun k => gs.map fun g => idx.getD (mulC E[k]! g) 0

meta def offs (l : List Nat) : List Nat :=
  (l.foldl (fun (acc : List Nat × Nat) n => ((n + acc.2) :: acc.1, n + acc.2)) ([0], 0)).1.reverse.dropLast

meta def eL : List Nat := gensL.flatMap fun gs => (elemsOf gs).toList
meta def pL : List Nat := gensL.flatMap parOf
meta def sL : List Nat := gensL.flatMap fun gs => sortOf (elemsOf gs)
meta def cL : List Nat := gensL.flatMap closOf
meta def nL : List Nat := gensL.map fun gs => (elemsOf gs).size
meta def gnL : List Nat := gensL.map List.length
meta def oL : List Nat := offs nL
meta def coL : List Nat := offs (gensL.map fun gs => (elemsOf gs).size * gs.length)
meta def gL : List Nat := gensL.flatMap fun gs => gs ++ List.replicate (8 - gs.length) 0

end CFSG.KC.Misc.GH23Gen

end
