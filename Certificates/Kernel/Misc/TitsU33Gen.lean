module

public meta import Std.Data.HashMap
public meta import Std.Data.HashSet

public section

namespace CFSG.KC.U33Gen

meta def mulM (a b : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    let row := (a >>> (6 * i)) &&& 63
    let mut acc := 0
    for k in [0:6] do
      if row.testBit k then acc := acc ^^^ ((b >>> (6 * k)) &&& 63)
    r := r ||| (acc <<< (6 * i))
  return r

meta def idM : Nat := 34630287489

meta def aM : Nat := 52078584193

meta def AM : Nat := 41615653681

meta def BM : Nat := 32279213243

meta def u0M : Nat := 43220222085

meta def t0M : Nat := 3724318459

meta def gs : Array Nat := #[aM, AM]

meta def gL : List Nat := gs.toList

meta def idxOf (E : Array Nat) : Std.HashMap Nat Nat :=
  (List.range E.size).foldl (fun m t => m.insert E[t]! t) {}

meta def bfs : Array Nat := Id.run do
  let mut E : Array Nat := #[idM]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert idM
  let mut p := 0
  while p < E.size do
    for g in gs do
      let c := mulM E[p]! g
      if !seen.contains c then
        E := E.push c
        seen := seen.insert c
    p := p + 1
  return E

meta def parents (E : Array Nat) : Array Nat := Id.run do
  let idx := idxOf E
  let mut par : Array Nat := Array.replicate E.size 0
  let mut done : Array Bool := (Array.replicate E.size false).set! 0 true
  for p in [0:E.size] do
    for l in [0:gs.size] do
      let t := idx.getD (mulM E[p]! gs[l]!) 0
      if t > p && !done[t]! then
        par := par.set! t (p + 2 ^ 24 * l)
        done := done.set! t true
  return par

meta def eL : List Nat := bfs.toList

meta def pL : List Nat := (parents bfs).toList

meta def cL : List Nat :=
  let idx := idxOf bfs
  (List.range bfs.size).flatMap fun k => gs.toList.map fun g => idx.getD (mulM bfs[k]! g) 0

meta def sL : List Nat := ((Array.range bfs.size).qsort fun x y => bfs[x]! < bfs[y]!).toList

meta def iA : Array Nat :=
  (Array.range bfs.size).filter fun k => let x := bfs[k]!; mulM x x == idM && x != idM

meta def oA : Array Nat :=
  (Array.range bfs.size).filter fun k => let y := mulM bfs[k]! BM; mulM y y == idM

meta def iL : List Nat := iA.toList

meta def oL : List Nat := oA.toList

meta def wL : List Nat :=
  let ii := idxOf iA
  let oi := idxOf oA
  (List.range bfs.size).map fun k => ii.getD k 0 + 2 ^ 10 * oi.getD k 0

meta def conjTo (r x : Nat) : Nat :=
  ((List.range bfs.size).find? fun g => mulM bfs[g]! r == mulM x bfs[g]!).getD 0

meta def cjI : List Nat := iL.map fun k => conjTo u0M bfs[k]!

meta def cjO : List Nat := oL.map fun k => conjTo t0M (mulM bfs[k]! BM)

meta def col0 (x : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => if x.testBit (6 * i) then acc ||| (1 <<< i) else acc) 0

meta def trL : List Nat :=
  (List.range 63).map fun n =>
    ((List.range bfs.size).find? fun k => col0 bfs[k]! == n + 1).getD 0

meta def rrL : List Nat :=
  let idx := idxOf bfs
  let ys := idxOf (bfs.map fun x => mulM x BM)
  [ys.getD (mulM BM AM) 0, idx.getD (mulM BM BM) 0, idx.getD u0M 0, ys.getD t0M 0]

end CFSG.KC.U33Gen

end
