module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.E6TableT
public import Certificates.Data.E6TableT

public section

namespace CertificateChecks.KernelE6TT.GenWeyl

open CFSG.KC.Eval Certificates.Data.E6TableT

meta def vsc (c : Int) (x y : Vec) : Vec := List.zipWith (fun a b => a + c * b) x y

meta def lin (cs : List Int) (Δ : List Vec) : Vec :=
  (cs.zip Δ).foldr (fun (c, δ) acc => vsc c acc δ) [0, 0, 0, 0, 0, 0]

meta partial def det (M : List (List Int)) : Int :=
  match M with
  | [] => 1
  | row :: rest => Id.run do
    let mut s : Int := 0
    for j in [0:row.length] do
      let minor := rest.map fun r => r.eraseIdx j
      let sg : Int := if j % 2 == 0 then 1 else -1
      s := s + sg * row.getD j 0 * det minor
    return s

meta def packD (w off : Nat) (xs : List Int) : Except String Nat := do
  let mut acc := 0
  for x in xs.reverse do
    let y := x + off
    unless 0 ≤ y && y < 2 ^ w do throw s!"digit {x} out of range"
    acc := acc * 2 ^ w + y.toNat
  return acc

meta def packVs (xs : List Vec) : Except String Nat := do
  let mut acc := 0
  for x in xs.reverse do
    acc := acc * 2 ^ 18 + (← packD 3 3 x)
  return acc

meta def classData (l : List Vec) : Except String (List Nat × List (List Nat)) := do
  let fn (x : Vec) : Int := (x.zipIdx.map fun (a, i) => a * 10 ^ i).sum
  let pos := l.filter fun x => fn x > 0
  let Δ := pos.filter fun x => !pos.any fun y => pos.contains (vsc (-1) x y)
  let r := Δ.length
  let G := Δ.map fun a => Δ.map fun b => iform a b
  let d := det G
  let deg (s : Nat) : Nat := ((List.range r).filter fun t => t != s && (G.getD s []).getD t 0 != 0).length
  let ends := (List.range r).filter fun s => deg s ≤ 1
  let gens ← if r ≥ 4 && l.length == 2 * r * (r - 1) then do
      let some br := (List.range r).find? fun s => deg s == 3 | throw "no branch node"
      let spin := ends.filter fun s => (G.getD s []).getD br 0 != 0
      pure (if r == 4 then spin.take 2 else spin.take 1)
    else pure (ends.take 1)
  let mut O : List (List Nat) := []
  for j in gens do
    let A : List Int := (List.range r).map fun t =>
      (if (j + t) % 2 == 0 then 1 else -1) *
        det ((G.eraseIdx j).map fun row => row.eraseIdx t)
    let W := lin A Δ
    let U := cartan.map (dot W)
    unless l.all (fun x => (dot x U) % d == 0) do throw "generator pairing"
    O := O ++ [[← packD 8 128 W, ← packD 8 128 A, ← packD 8 128 U]]
  let mut coef : List (Vec × List Int) :=
    (List.range r).map fun t => (Δ.getD t [], (List.range r).map fun s => if s == t then 1 else 0)
  let mut frontier := coef
  while !frontier.isEmpty do
    let mut next := []
    for (β, c) in frontier do
      for t in [0:r] do
        let γ := vsc 1 β (Δ.getD t [])
        if pos.contains γ && !(coef.any fun p => p.1 == γ) then
          let e := (c.zipIdx.map fun (a, s) => if s == t then a + 1 else a)
          coef := coef ++ [(γ, e)]
          next := next ++ [(γ, e)]
    frontier := next
  let mut CF := 0
  for (x, i) in l.zipIdx do
    let c ← match coef.find? (fun p => p.1 == x) with
      | some p => pure p.2
      | none => match coef.find? (fun p => p.1 == vsc (-1) [0, 0, 0, 0, 0, 0] x) with
        | some p => pure (p.2.map fun a => -a)
        | none => throw "root not in the span"
    unless lin c Δ == x do throw "coordinates"
    CF := CF + (← packD 3 3 c) * 2 ^ (16 * i)
  let mut ents : Array (List Vec × Nat × Nat × Nat) := #[(Δ, 0, 0, 0)]
  let mut keys : Std.HashMap Nat Nat := {}
  keys := keys.insert (← packVs Δ) 0
  let mut lo := 0
  while lo < ents.size do
    let hi := ents.size
    for p in [lo:hi] do
      let (X, _, _, dp) := ents[p]!
      for s in [0:r] do
        let gs := G.getD s []
        let Y := List.zipWith (fun g x => vsc (-g) x (X.getD s [])) gs X
        let k ← packVs Y
        unless keys.contains k do
          keys := keys.insert k ents.size
          ents := ents.push (Y, p, s, dp + 1)
    lo := hi
  let n := ents.size
  let mut ks : Array (Nat × Nat) := #[]
  for i in [0:n] do
    ks := ks.push (← packVs ents[i]!.1, i)
  let sorted := ks.qsort (fun a b => a.1 < b.1)
  let mut posOf : Array Nat := Array.replicate n 0
  for i in [0:n] do
    posOf := posOf.set! sorted[i]!.2 i
  let w := 18 * r
  let mut TK := 0
  let mut TM := 0
  for i in [0:n] do
    let (key, b) := sorted[i]!
    let (_, p, s, dp) := ents[b]!
    unless dp < 32 && s < 8 && n ≤ 4096 do throw "table field out of range"
    TK := TK + key * 2 ^ (w * i)
    TM := TM + (dp + 32 * s + 256 * posOf[p]!) * 2 ^ (24 * i)
  return ([r, d.toNat, ← packVs Δ, TK, TM, n, CF], O)

public meta def weylRecs (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let mut out : Array (Lean.Name × Val) := #[]
  for k in [0:5] do
    let cl := classes (reps.getD k [])
    let mut Hs : Array Val := #[]
    let mut Os : Array Val := #[]
    for l in cl do
      let (H, O) ← classData l
      Hs := Hs.push (.list (H.toArray.map .nat))
      Os := Os.push (.list (O.toArray.map fun o => .list (o.toArray.map .nat)))
    out := out.push (Lean.Name.mkSimple s!"H{k}", .list Hs)
    out := out.push (Lean.Name.mkSimple s!"O{k}", .list Os)
  return out

end CertificateChecks.KernelE6TT.GenWeyl

end
