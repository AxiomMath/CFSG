module

public import Certificates.Kernel.HNClsL.Data
public meta import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Kernel.LocalQT.Cmd
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.HNClsL.Ev

open CFSG.KC.Eval CFSG.KC.LQT.Cmd

meta def natV (v : Val) : Except String Nat :=
  match v with
  | .nat n => pure n
  | _ => throw "expected a number"

meta def listV (v : Val) : Except String (Array Val) :=
  match v with
  | .list xs => pure xs
  | _ => throw "expected a list"

meta def natsV (v : Val) : Except String (Array Nat) := do
  (← listV v).mapM natV

meta def specV (v : Val) : Except String (Array (Nat × Nat)) := do
  (← listV v).mapM fun p => do
    let q ← natsV p
    if q.size != 2 then throw "expected a pair"
    pure (q[0]!, q[1]!)

meta def invWM (cs : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for c in cs.reverse do
    out := out ++ (if c < 17 then #[c + 17] else if c < 34 then #[c - 17]
      else if c == 35 then #[35, 35] else #[c])
  return out

meta def repair (ws0 : Array (Array Nat)) : Array (Array Nat) × Array (Nat × Nat) := Id.run do
  let mut ws := ws0
  let mut rules : Array (Nat × Nat) := #[]
  for _ in [0:100000] do
    let mut ks0 : Array Nat := #[]
    for w in ws do
      for i in [0:w.size - 1] do
        ks0 := ks0.push (w[i]! * 65536 + w[i + 1]!)
    let ks := ks0.qsort (· < ·)
    let mut best := 0
    let mut bn := 0
    let mut i := 0
    while i < ks.size do
      let mut j := i
      while j < ks.size && ks[j]! == ks[i]! do j := j + 1
      if j - i > bn then
        best := ks[i]!
        bn := j - i
      i := j
    if bn < 2 then break
    let a := best / 65536
    let b := best % 65536
    let x := 37 + rules.size
    rules := rules.push (a, b)
    ws := ws.map fun w => Id.run do
      let mut out : Array Nat := #[]
      let mut i := 0
      while i < w.size do
        if i + 1 < w.size && w[i]! == a && w[i + 1]! == b then
          out := out.push x
          i := i + 2
        else
          out := out.push w[i]!
          i := i + 1
      return out
  return (ws, rules)

meta def run (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 46 then throw "run: expected 46 arguments"
  let pool ← (← listV args[0]!).mapM natsV
  let lo ← natV args[44]!
  let hi ← natV args[45]!
  let used (j : Nat) : Bool := lo ≤ j && j < hi
  let gens ← natsV args[1]!
  let lines ← (← listV args[2]!).mapM specV
  let wl ← (← listV args[3]!).mapM specV
  let tr ← natsV args[4]!
  let ONE ← natV args[5]!
  let useSlp ← natV args[6]!
  let L0 ← (args.extract 7 44).mapM natV
  let c := layOf 5 133
  if c.ONE != ONE then throw "run: ONE is not the identity of the layout"
  let invs := (List.range pool.size).toArray.map fun j => if used j then invWM pool[j]! else #[]
  let (mw0, rules) := if useSlp == 1 then repair pool
    else if useSlp == 2 then repair (pool ++ invs) else (pool, #[])
  let mw := mw0.extract 0 pool.size
  let iw := if useSlp == 2 then mw0.extract pool.size (2 * pool.size) else invs
  let mut L := L0
  let mut X : Array (Array Nat) := (List.range 37).toArray.map fun l => #[l]
  for (a, b) in rules do
    L := L.push (c.mul L[a]! L[b]!)
    X := X.push (X[a]! ++ X[b]!)
  let mk (s : String) : Lean.Name := .mkSimple s
  let mut out : Array (Lean.Name × Val) := #[(`one, .nat ONE)]
  out := out.push (`NR, .nat rules.size)
  out := out.push (`RA, .list (rules.map fun r => .nat r.1))
  out := out.push (`RB, .list (rules.map fun r => .nat r.2))
  out := out.push (`RV, .list ((L.extract 37 L.size).map Val.nat))
  for k in [0:rules.size] do
    out := out.push (mk s!"RX{k}", .list (X[37 + k]!.map Val.nat))
  out := out.push (`RXL, .list ((List.range rules.size).map fun k => Val.ref (mk s!"RX{k}")).toArray)
  let mut F : Array Nat := #[]
  let mut G : Array Nat := #[]
  let mut pm : Array Val := #[]
  let mut gl : Array Val := #[]
  for j in [0:pool.size] do
    out := out.push (mk s!"MW{j}", .list (mw[j]!.map Val.nat))
  out := out.push (`MWL, .list ((List.range pool.size).map fun j => Val.ref (mk s!"MW{j}")).toArray)
  for j in [0:pool.size] do
    if !used j then
      out := out.push (mk s!"GP{j}", .list #[.ref `one])
      gl := gl.push (.ref `one)
    for (t, w) in (if used j then [("f", mw[j]!), ("g", iw[j]!)] else [("f", mw[j]!)]) do
      let mut acc := ONE
      let mut ps : Array Val := #[.ref `one]
      let mut i := 0
      let mut nm : Lean.Name := `one
      for l in w do
        acc := c.mul acc (L.getD l ONE)
        i := i + 1
        if i % 32 == 0 || i == w.size then
          nm := mk s!"{t}{j}_{(i + 31) / 32}"
          out := out.push (nm, .nat acc)
          ps := ps.push (.ref nm)
      out := out.push (mk s!"{t.toUpper}P{j}", .list ps)
      if t == "f" then
        F := F.push acc
        pm := pm.push (.ref nm)
      else
        G := G.push acc
        gl := gl.push (.ref nm)
  out := out.push (`PM, .list pm)
  out := out.push (`GL, .list gl)
  out := out.push (`FPL, .list ((List.range pool.size).map fun j => Val.ref (mk s!"FP{j}")).toArray)
  out := out.push (`GPL, .list ((List.range pool.size).map fun j => Val.ref (mk s!"GP{j}")).toArray)
  for j in [0:pool.size] do
    out := out.push (mk s!"IW{j}", .list (iw[j]!.map Val.nat))
  out := out.push (`IWL, .list ((List.range pool.size).map fun j => Val.ref (mk s!"IW{j}")).toArray)
  let Fj (j : Nat) : Nat := F.getD j ONE
  let powM (X e : Nat) : Nat := Id.run do
    let mut acc := ONE
    for _ in [0:e] do acc := c.mul acc X
    return acc
  let specM (s : Array (Nat × Nat)) : Nat :=
    s.foldl (fun acc (j, e) => c.mul acc (powM (Fj j) e)) ONE
  let GM := gens.map Fj
  let mut ks : Array Nat := #[ONE]
  let mut kr : Array Val := #[.ref `one]
  let mut h := 0
  let mut l := 0
  for t in tr do
    let x := c.mul (GM.getD l ONE) (ks.getD h ONE)
    if t == 0 then
      out := out.push (mk s!"k{ks.size}", .nat x)
      kr := kr.push (.ref (mk s!"k{ks.size}"))
      ks := ks.push x
    if l + 1 == GM.size then
      h := h + 1
      l := 0
    else
      l := l + 1
  out := out.push (`KS, .list kr.reverse)
  let mut pks : Array Val := #[]
  for i in [0:lines.size] do
    let x := specM lines[i]!
    let mut y := x
    let mut row : Array Val := #[]
    for e in [1:5] do
      out := out.push (mk s!"l{i}_{e}", .nat y)
      row := row.push (.ref (mk s!"l{i}_{e}"))
      y := c.mul y x
    pks := pks.push (.list row)
  out := out.push (`PKS, .list pks)
  let mut wm : Array Val := #[]
  for i in [0:wl.size] do
    out := out.push (mk s!"m{i}", .nat (specM wl[i]!))
    wm := wm.push (.ref (mk s!"m{i}"))
  out := out.push (`WM, .list wm)
  return out

end CFSG.KD.HNClsL.Ev

#kc_repo #kc_json CFSG.KD.HNClsL.J "Certificates/Kernel/HNClsL/data/hncls.json" 16602 870290615336731402
    (linesA : List (List (List Nat))) (wlA : List (List (List Nat)))
    (linesB : List (List (List Nat))) (wlB : List (List (List Nat)))
    (linesC : List (List (List Nat))) (wlC : List (List (List Nat)))

#kc_eval CFSG.KD.HNClsL SA CFSG.KD.HNClsL.Ev.run poolA gensA J.linesA J.wlA trA CFSG.KD.OrdHN.ONE 1
  CFSG.KD.HNPt.R0 CFSG.KD.HNPt.R1 CFSG.KD.HNPt.R2 CFSG.KD.HNPt.R3 CFSG.KD.HNPt.R4 CFSG.KD.HNPt.R5
  CFSG.KD.HNPt.R6 CFSG.KD.HNPt.R7 CFSG.KD.HNPt.R8 CFSG.KD.HNPt.R9 CFSG.KD.HNPt.R10
  CFSG.KD.HNPt.R11 CFSG.KD.HNPt.R12 CFSG.KD.HNPt.R13 CFSG.KD.HNPt.R14 CFSG.KD.HNPt.R15
  CFSG.KD.HNPt.R16 CFSG.KD.HNPt.R17 CFSG.KD.HNPt.R18 CFSG.KD.HNPt.R19 CFSG.KD.HNPt.R20
  CFSG.KD.HNPt.R21 CFSG.KD.HNPt.R22 CFSG.KD.HNPt.R23 CFSG.KD.HNPt.R24 CFSG.KD.HNPt.R25
  CFSG.KD.HNPt.R26 CFSG.KD.HNPt.R27 CFSG.KD.HNPt.R28 CFSG.KD.HNPt.R29 CFSG.KD.HNPt.R30
  CFSG.KD.HNPt.R31 CFSG.KD.HNPt.R32 CFSG.KD.HNPt.R33 CFSG.KD.HNPt.R34 CFSG.KD.HNPt.R35
  CFSG.KD.HNPtC.GT10 4 11

#kc_eval CFSG.KD.HNClsL SB CFSG.KD.HNClsL.Ev.run poolB gensB J.linesB J.wlB trB CFSG.KD.OrdHN.ONE 2
  CFSG.KD.HNPt.R0 CFSG.KD.HNPt.R1 CFSG.KD.HNPt.R2 CFSG.KD.HNPt.R3 CFSG.KD.HNPt.R4 CFSG.KD.HNPt.R5
  CFSG.KD.HNPt.R6 CFSG.KD.HNPt.R7 CFSG.KD.HNPt.R8 CFSG.KD.HNPt.R9 CFSG.KD.HNPt.R10
  CFSG.KD.HNPt.R11 CFSG.KD.HNPt.R12 CFSG.KD.HNPt.R13 CFSG.KD.HNPt.R14 CFSG.KD.HNPt.R15
  CFSG.KD.HNPt.R16 CFSG.KD.HNPt.R17 CFSG.KD.HNPt.R18 CFSG.KD.HNPt.R19 CFSG.KD.HNPt.R20
  CFSG.KD.HNPt.R21 CFSG.KD.HNPt.R22 CFSG.KD.HNPt.R23 CFSG.KD.HNPt.R24 CFSG.KD.HNPt.R25
  CFSG.KD.HNPt.R26 CFSG.KD.HNPt.R27 CFSG.KD.HNPt.R28 CFSG.KD.HNPt.R29 CFSG.KD.HNPt.R30
  CFSG.KD.HNPt.R31 CFSG.KD.HNPt.R32 CFSG.KD.HNPt.R33 CFSG.KD.HNPt.R34 CFSG.KD.HNPt.R35
  CFSG.KD.HNPtC.GT10 3 8

#kc_eval CFSG.KD.HNClsL SC CFSG.KD.HNClsL.Ev.run poolC gensC J.linesC J.wlC trC CFSG.KD.OrdHN.ONE 2
  CFSG.KD.HNPt.R0 CFSG.KD.HNPt.R1 CFSG.KD.HNPt.R2 CFSG.KD.HNPt.R3 CFSG.KD.HNPt.R4 CFSG.KD.HNPt.R5
  CFSG.KD.HNPt.R6 CFSG.KD.HNPt.R7 CFSG.KD.HNPt.R8 CFSG.KD.HNPt.R9 CFSG.KD.HNPt.R10
  CFSG.KD.HNPt.R11 CFSG.KD.HNPt.R12 CFSG.KD.HNPt.R13 CFSG.KD.HNPt.R14 CFSG.KD.HNPt.R15
  CFSG.KD.HNPt.R16 CFSG.KD.HNPt.R17 CFSG.KD.HNPt.R18 CFSG.KD.HNPt.R19 CFSG.KD.HNPt.R20
  CFSG.KD.HNPt.R21 CFSG.KD.HNPt.R22 CFSG.KD.HNPt.R23 CFSG.KD.HNPt.R24 CFSG.KD.HNPt.R25
  CFSG.KD.HNPt.R26 CFSG.KD.HNPt.R27 CFSG.KD.HNPt.R28 CFSG.KD.HNPt.R29 CFSG.KD.HNPt.R30
  CFSG.KD.HNPt.R31 CFSG.KD.HNPt.R32 CFSG.KD.HNPt.R33 CFSG.KD.HNPt.R34 CFSG.KD.HNPt.R35
  CFSG.KD.HNPtC.GT10 3 10
