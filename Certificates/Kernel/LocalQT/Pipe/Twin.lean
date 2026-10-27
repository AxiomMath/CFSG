module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public meta import Lean
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KD.LQT.PipeTwin

open CFSG.KC.Tab CFSG.QuasithinUnique.Setup.X1

meta def compA (s t : Array Nat) : Array Nat := t.map fun j => s[j]!

meta partial def packR (w : Nat) (a : Array Nat) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 16 then Id.run do
    let mut acc := 0
    for k in [0:hi - lo] do
      acc := acc ||| (a[lo + k]! <<< (w * k))
    return acc
  else
    let mid := (lo + hi) / 2
    packR w a lo mid ||| (packR w a mid hi <<< (w * (mid - lo)))

meta def pk (w : Nat) (a : Array Nat) : Nat := packR w a 0 a.size

meta def maskOf (l : Array Nat) : Nat := l.foldl (fun m x => m ||| (1 <<< x)) 0

meta def natListE (l : Array Nat) : Expr :=
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

meta def natListListE (l : Array (Array Nat)) : Expr :=
  let ty := mkApp (mkConst ``List [0]) natT
  l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty (natListE x) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

meta def addTreeT (F : Name) (vs : Array Nat) : CoreM Unit := do
  let h := Nat.log2 (2 * max vs.size 1 - 1)
  addDef (F ++ `Z) natT (lit 0)
  for k in [0:vs.size] do
    addDef (F ++ Name.mkSimple s!"L{k}") natT (lit vs[k]!)
  addDef F fnT (table (fun k => constFn (mkConst (if k < vs.size then
    F ++ Name.mkSimple s!"L{k}" else F ++ `Z))) (1 <<< h) 0)

meta def bfsOrd (N : Nat) (ts : Array (Array Nat)) (s : Nat) : Array Nat := Id.run do
  let mut vis := (Array.replicate N false).set! s true
  let mut ord : Array Nat := #[s]
  let mut k := 0
  while k < ord.size do
    let x := ord[k]!
    k := k + 1
    for t in ts do
      let y := t[x]!
      if !vis[y]! then
        vis := vis.set! y true
        ord := ord.push y
  return ord

meta def quotEdges (N : Nat) (ts : Array (Array Nat)) (rep : Array Nat) (mem : Array (Array Nat)) :
    Array Nat := Id.run do
  let mut seen := (Array.replicate N false).set! rep[0]! true
  let mut q : Array Nat := #[rep[0]!]
  let mut k := 0
  let mut es : Array Nat := #[]
  while k < q.size do
    let r := q[k]!
    k := k + 1
    for y in mem[r]! do
      for gi in [0:ts.size] do
        let r' := rep[ts[gi]![y]!]!
        if !seen[r']! then
          seen := seen.set! r' true
          q := q.push r'
          es := es.push (y * 8 + gi)
  return es

meta def bfsGTwin (o : Array Nat) (G : Array (Array Nat)) : Array (Array Nat) × Nat := Id.run do
  let mut seen : Std.HashSet (Array Nat) := ({} : Std.HashSet (Array Nat)).insert o
  let mut elems : Array (Array Nat) := #[o]
  let mut fr : Array (Array Nat) := #[o]
  let mut d := 0
  while fr.size > 0 do
    let mut nf : Array (Array Nat) := #[]
    for x in fr do
      for g in G do
        let y := compA x g
        if !seen.contains y then
          seen := seen.insert y
          elems := elems.push y
          nf := nf.push y
    if nf.size > 0 then d := d + 1
    fr := nf.reverse
  return (elems.reverse, d)

end CFSG.KD.LQT.PipeTwin

open CFSG.KC.Tab CFSG.KD.LQT.PipeTwin CFSG.QuasithinUnique.Setup.X1 in
elab "#pipe_twin " pre:ident dId:ident : command => do
  let P := pre.getId
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let D ← liftTermElabM <| unsafe evalConst PipeData dN
  let N := D.N
  let W := 13
  let w := 9
  let n := D.n
  let prog := D.prog.toArray
  let mut T : Array (Array Nat) := #[D.Aa, D.Ab]
  for p in prog do
    T := T.push (compA T[p.1]! T[p.2]!)
  let mut need := Array.replicate T.size false
  let mut st : Array Nat := D.qp.toArray.map (·.1)
  while st.size > 0 do
    let j := st.back!
    st := st.pop
    if j ≥ 2 && !need[j]! then
      need := need.set! j true
      st := st.push prog[j - 2]!.1
      st := st.push prog[j - 2]!.2
  let SL := (Array.range T.size).filter fun j => need[j]!
  let TFv := (Array.range T.size).map fun j => if j < 2 || need[j]! then pk W T[j]! else 0
  let ROm := D.qp.toArray.map fun p => T[p.1]!
  let rep := D.repR
  let REPS := (rep.toList.eraseDups.toArray.qsort (· < ·))
  let mut ridx := Array.replicate N 0
  for c in [0:REPS.size] do
    ridx := ridx.set! REPS[c]! c
  let mut mem : Array (Array Nat) := Array.replicate N #[]
  for i in [0:N] do
    mem := mem.modify rep[i]! (·.push i)
  let mut qpar := Array.replicate N 0
  let mut qgen := Array.replicate N 0
  let mut dep := Array.replicate N 0
  for r in REPS do
    let mut vis := (Array.replicate N false).set! r true
    let mut q : Array Nat := #[r]
    let mut k := 0
    while k < q.size do
      let x := q[k]!
      k := k + 1
      for gi in [0:ROm.size] do
        let y := ROm[gi]![x]!
        if !vis[y]! then
          vis := vis.set! y true
          q := q.push y
          qpar := qpar.set! y x
          qgen := qgen.set! y gi
          dep := dep.set! y (dep[x]! + 1)
  let OML := REPS.map fun r => maskOf mem[r]!
  let par := D.par
  let gen := D.gen
  let mut needM := Array.replicate N false
  for x in REPS.toList ++ (D.xs.toList.foldl (· ++ ·) []) do
    let mut y := x
    while y != 0 && !needM[y]! do
      needM := needM.set! y true
      y := par[y]!
  let ML := (Array.range N).filter fun x => needM[x]!
  let mut OM : Array (Array Nat) := Array.replicate N #[]
  OM := OM.set! 0 (Array.range N)
  for x in ML do
    OM := OM.set! x (compA (if gen[x]! == 0 then D.Aa else D.Ab) OM[par[x]!]!)
  let MFv := (Array.range N).map fun x => if x == 0 || needM[x]! then pk W OM[x]! else 0
  let full := (1 <<< N) - 1
  let cert := fun (ts : Array (Array Nat)) =>
    let o := bfsOrd N ts 0
    if o.size == N then (full, quotEdges N ts rep mem) else (maskOf o, o)
  let gensOf := fun (l : List Nat) => ROm ++ l.toArray.map fun x => OM[x]!
  let blocks := D.xs.map fun l => cert (gensOf l)
  let BM := blocks.map (·.1)
  let mut PWL : Array (Array Nat) := #[]
  for l in D.xs do
    for x in REPS do
      let (m, c) := cert (gensOf l ++ #[OM[x]!])
      let some k := BM.findIdx? (· == m) | throwError "pipe_twin: an orbit is not a block"
      PWL := PWL.push (#[k] ++ c)
  let size := fun (m : Nat) => (Array.range N).foldl (fun c i => if (m >>> i) % 2 == 1 then c + 1
    else c) 0
  let sub := fun (a b : Nat) => a &&& b == a
  let mut sh : Option (Nat × Nat) := none
  for h1 in [0:BM.size] do
    for h2 in [0:BM.size] do
      if sh.isNone && BM[h1]! != full && BM[h2]! != full && size BM[h1]! != size BM[h2]! &&
          BM.all (fun b => !sub BM[h1]! b || sub b BM[h1]! || b == full) &&
          BM.all (fun b => !sub BM[h2]! b || sub b BM[h2]! || b == full) &&
          BM.all (fun b => b == full || sub b BM[h1]! || sub b BM[h2]!) then
        sh := some (h1, h2)
  let some (h1, h2) := sh | throwError "pipe_twin: no shape witnesses"
  let mut RT : Array (Array Nat) := #[Array.range n]
  for i in [1:N] do
    RT := RT.push (compA (if gen[i]! == 0 then D.ta else D.tb) RT[par[i]!]!)
  let mut NT : Array (Array Nat) := #[D.ta, D.tb]
  for p in prog do
    NT := NT.push (compA NT[p.1]! NT[p.2]!)
  let (els, dR) := bfsGTwin (Array.range n) (D.qp.toArray.map fun p => NT[p.1]!)
  logInfo m!"pipe_twin: |SL| {SL.size}, |ML| {ML.size}, |REPS| {REPS.size}, blocks {BM.size}, \
    pairs {PWL.size}, rounds {dR}, |R| {els.size}, shape {h1} {h2}"
  liftCoreM <| withOptions (Elab.async.set · false) do
    let listT := mkApp (mkConst ``List [0]) natT
    let listLT := mkApp (mkConst ``List [0]) listT
    addTreeT (P ++ `TF) TFv
    addTreeT (P ++ `MF) MFv
    addTreeT (P ++ `RF) (RT.map (pk w))
    addDef (P ++ `SL) listT (natListE SL)
    addDef (P ++ `ML) listT (natListE ML)
    addDef (P ++ `REPS) listT (natListE REPS)
    addDef (P ++ `OML) listT (natListE OML)
    addDef (P ++ `BM) listT (natListE BM)
    addDef (P ++ `BWL) listLT (natListListE (blocks.map (·.2)))
    addDef (P ++ `PWL) listLT (natListListE PWL)
    addDef (P ++ `RL) listT (natListE (els.map (pk w)))
    addDef (P ++ `dR) natT (lit dR)
    addDef (P ++ `SH1) natT (lit h1)
    addDef (P ++ `SH2) natT (lit h2)
    addDef (P ++ `RPK) natT (lit (pk W rep))
    addDef (P ++ `PRK) natT (lit (pk W par))
    addDef (P ++ `GNK) natT (lit (pk W gen))
    addDef (P ++ `RIK) natT (lit (pk W ((Array.range N).map fun i => ridx[rep[i]!]!)))
    addDef (P ++ `QPK) natT (lit (pk W qpar))
    addDef (P ++ `QGK) natT (lit (pk W qgen))
    addDef (P ++ `DPK) natT (lit (pk W dep))

end
