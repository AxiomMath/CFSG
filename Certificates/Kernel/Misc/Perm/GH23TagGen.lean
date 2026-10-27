module

public meta import Certificates.Kernel.Misc.Perm.GH23Gen
public import Certificates.Data.GH23Data
public import Certificates.Kernel.Misc.Perm.GH23Gen

public section

namespace CFSG.KC.Misc.GH23TagGen

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.KC.Misc.GH23Gen

meta def extraOf : Tag → List (List Nat)
  | .solv chain => chain
  | .two ngens => [ngens]
  | .alt _ imgs => [imgs]
  | .sym _ imgs => [imgs]
  | .z3a5 imgs z => [imgs ++ [z]]
  | _ => []

meta def xgensL : List (List Nat) := members.flatMap fun m => extraOf m.tag

meta def xbL : List Nat := (offs (members.map fun m => (extraOf m.tag).length)).map (· + 42)

meta def refGens (r : Nat) : List Nat :=
  if r < 42 then gensL.getD r [] else xgensL.getD (r - 42) []

meta def eXL : List Nat := xgensL.flatMap fun gs => (elemsOf gs).toList
meta def pXL : List Nat := xgensL.flatMap parOf
meta def sXL : List Nat := xgensL.flatMap fun gs => sortOf (elemsOf gs)
meta def cXL : List Nat := xgensL.flatMap closOf
meta def nXL : List Nat := xgensL.map fun gs => (elemsOf gs).size
meta def gnXL : List Nat := xgensL.map List.length
meta def oXL : List Nat := offs nXL
meta def coXL : List Nat := offs (xgensL.map fun gs => (elemsOf gs).size * gs.length)
meta def gXL : List Nat := xgensL.flatMap fun gs => gs ++ List.replicate (8 - gs.length) 0

meta def jobsOf (mi xb : Nat) : Tag → List (Nat × Nat)
  | .solv chain => (List.range chain.length).map fun k => (if k = 0 then mi else xb + k - 1, xb + k)
  | _ => []

meta def jobsM : List (List (Nat × Nat)) :=
  (List.range 41).map fun mi => jobsOf mi (xbL.getD mi 0) (members.getD mi ⟨[], .top⟩).tag

meta def jobs : List (Nat × Nat) := jobsM.flatten

meta def commOf (p : Nat × Nat) : List Nat :=
  let EA := (elemsOf (refGens p.1)).toList
  let iB := indexOf (elemsOf (refGens p.2))
  EA.flatMap fun x => EA.map fun y => iB.getD (mulC (mulC (mulC x y) (invC x)) (invC y)) 0

meta def jL : List Nat := jobs.flatMap fun p => [p.1, p.2]
meta def jbL : List Nat := offs (jobsM.map List.length)
meta def joL : List Nat := offs (jobs.map fun p => (elemsOf (refGens p.1)).size ^ 2)
meta def cwL : List Nat := jobs.flatMap commOf

meta def phiOf (gs imgs : List Nat) : Std.HashMap Nat Nat :=
  (bfsChain gs).foldl (fun acc t =>
      acc.insert t.1 (mulC (acc.getD t.2.1 0) (imgs.getD (posOf gs t.2.2) 0)))
    (({} : Std.HashMap Nat Nat).insert oneC oneC)

meta def witOf (m : MemberData) : List Nat :=
  let P := m.gens
  let iP := indexOf (elemsOf P)
  match m.tag with
  | .two ngens =>
    let iN := indexOf (elemsOf ngens)
    ngens.map (iP.getD · 0) ++ P.flatMap fun g => ngens.flatMap fun n =>
      [iN.getD (mulC (mulC g n) (invC g)) 0, iN.getD (mulC (mulC (invC g) n) g) 0]
  | .alt _ imgs | .sym _ imgs =>
    let iI := indexOf (elemsOf imgs)
    imgs.map (iP.getD · 0) ++ P.map (iI.getD · 0)
  | .z3a5 imgs z =>
    let iI := indexOf (elemsOf (imgs ++ [z]))
    (imgs ++ [z]).map (iP.getD · 0) ++ P.map (iI.getD · 0)
  | .idx2 j => (members.getD j ⟨[], .top⟩).gens.map (iP.getD · 0)
  | .gl imgs =>
    let phi := phiOf P imgs
    let iQ := indexOf (elemsOf q2gens)
    let fi := (elemsOf P).toList.map fun x => iQ.getD (phi.getD x 0) 0
    fi ++ (List.range 168).map fun t => fi.idxOf t
  | _ => []

meta def wM : List (List Nat) := members.map witOf
meta def wL : List Nat := wM.flatten
meta def woL : List Nat := offs (wM.map List.length)

meta def cntL : List Nat := [xgensL.length, jobs.length]

end CFSG.KC.Misc.GH23TagGen

end
