module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LargeExtraspecial.S14SMKTransCheck

namespace CertificateChecks.KernelSmithEK

open CFSG.KC.Eval CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

meta def fpScaleM (l c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + f4mul l (coord c i) * 4 ^ i) 0

meta def f4invM (x : Nat) : Nat := [0, 1, 3, 2].getD x 0

meta def fpUnits (FC : List Nat) : Except String (List (List Nat)) := do
  let n := FC.length
  let mut rows : Array (Nat × Array Nat) := (FC.zipIdx.map fun (c, i) =>
    (c, (Array.replicate n 0).set! i 1)).toArray
  let mut piv : Array Nat := Array.replicate 6 n
  let mut used : Array Bool := Array.replicate n false
  for col in [0:6] do
    match (List.range n).find? fun r => !used[r]! && coord rows[r]!.1 col != 0 with
    | none => throw s!"fpUnits: no pivot in column {col}"
    | some r =>
      let s := f4invM (coord rows[r]!.1 col)
      let row := (fpScaleM s rows[r]!.1, rows[r]!.2.map (f4mul s))
      rows := rows.set! r row
      used := used.set! r true
      piv := piv.set! col r
      for r' in [0:n] do
        if r' != r then
          let e := coord rows[r']!.1 col
          if e != 0 then
            rows := rows.set! r' (rows[r']!.1 ^^^ fpScaleM e row.1,
              (Array.range n).map fun i => rows[r']!.2[i]! ^^^ f4mul e row.2[i]!)
  let mut out : List (List Nat) := []
  for col in [0:6] do
    let r := piv[col]!
    if rows[r]!.1 != 4 ^ col then throw s!"fpUnits: column {col} not a unit"
    out := out ++ [(List.range n).filterMap fun i =>
      if rows[r]!.2[i]! == 0 then none else some (i + 64 * rows[r]!.2[i]!)]
  return out

public meta def fpStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "fpStep: expected no arguments"
  let T := tvTabs
  let P := uaPts
  let W0 := P[0]!
  let W := wtArr
  let F := uaFlags P
  let PP := uaPtPlanes P
  let U := uPts ()
  let nat1 := fun (l : List Nat) => Val.list (l.toArray.map .nat)
  let mut out : Array (Array Val) := Array.replicate 10 #[]
  for j in [2:5] do
    let c := candT T W0 (liftTab T j) 19
    let sg := sigT F PP P c
    let st := (List.range 891).foldl (fun (st : List (Nat × Nat) × List Nat) i =>
      let w := echRed st.1 (W[i]!, 0)
      if w.1 == 0 then st else (echIns st.1 w, st.2 ++ [i])) ([], [])
    let PI := st.2
    if PI.length != 20 then throw s!"fpStep: {PI.length} independent planes"
    let PJ := PI.map fun i => sg[i]!
    let EW := (echOf (PI.map fun i => W[i]!)).1
    let UM := (List.range 20).map fun t => maskOf EW (2 ^ t)
    let ds := (List.range 891).map (dVec W sg)
    let BS := pickIndep ds 8
    let EB := (echOf BS).1
    let BM := (PI.zip PJ).map fun (i, i') => maskOf EB (W[i']! ^^^ W[i]!)
    let fx := fixL c
    let mut ord : Array Nat := #[fx.headD 0]
    let mut fe : Array Nat := #[]
    let mut k := 0
    while k < ord.size do
      let u := ord[k]!
      for g in [0:fx.length] do
        if ord.size ≤ 63 then
          let v := ap T[fx[g]!]! u
          if !ord.contains v then
            ord := ord.push v
            fe := fe.push (g + 64 * k)
      k := k + 1
    if ord.size != fx.length then throw "fpStep: the fixed points are not one orbit"
    let FX := ord.toList
    let FE := fe.toList.map fun e =>
      (FX.idxOf (fx[e % 64]!)) + 64 * (e / 64)
    let FC := FX.map fun x => U[x]!
    let FL ← (List.range (FC.length - 1)).mapM fun k => do
      let x := FC[k + 1]!
      let hit := (List.range FC.length).flatMap fun n => [1, 2, 3].flatMap fun l =>
        [1, 2, 3].filterMap fun u =>
          if FC[n]! == (fpScaleM l FC[0]! ^^^ fpScaleM u x) then some (64 * n + 4096 * l + 16384 * u)
          else none
      match hit with
      | e :: _ => pure e
      | [] => throw s!"fpStep: no line through {FX[0]!}, {FX[k + 1]!}"
    let SP ← fpUnits FC
    let vals : Array Val := #[nat1 PI, nat1 PJ, nat1 UM, nat1 BS, nat1 BM, nat1 FX, nat1 FC,
      nat1 FE, nat1 FL, .list (SP.toArray.map nat1)]
    out := (Array.range 10).map fun f => out[f]!.push vals[f]!
  let names := #[`PI, `PJ, `UM, `BS, `BM, `FX, `FC, `FE, `FL, `SP]
  return (Array.range 10).map fun f => (names[f]!, .list out[f]!)

end CertificateChecks.KernelSmithEK
