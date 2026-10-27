module

public meta import Std.Data.HashMap

public section

namespace CertificateChecks.KernelSporSch.Co2M.Gen

meta def m22 : Nat := 4194303

meta def lw : Nat := (List.range 22).foldl (fun a i => a ||| (1 <<< (22 * i))) 0

meta def mulP (X Y : Nat) : Nat := Id.run do
  let mut acc := 0
  for c in [0:22] do
    acc := acc ^^^ (((X >>> c) &&& lw) * ((Y >>> (22 * c)) &&& m22))
  return acc

meta def vm (v X : Nat) : Nat := Id.run do
  let mut acc := 0
  for k in [0:22] do
    if (v >>> k) &&& 1 == 1 then acc := acc ^^^ ((X >>> (22 * k)) &&& m22)
  return acc

meta def basisOf (V : Array Nat) : Array (List Nat) := Id.run do
  let mut piv : Array (Nat × Nat) := Array.replicate 22 (0, 0)
  for i in [0:V.size] do
    let mut v := V[i]!
    let mut s := 1 <<< i
    for b' in [0:22] do
      let b := 21 - b'
      if (v >>> b) &&& 1 == 1 && (piv[b]!).1 != 0 then
        v := v ^^^ (piv[b]!).1
        s := s ^^^ (piv[b]!).2
    if v != 0 then
      piv := piv.set! v.log2 (v, s)
  let mut out : Array (List Nat) := #[]
  for r in [0:22] do
    let mut v := 1 <<< r
    let mut s := 0
    for b' in [0:22] do
      let b := 21 - b'
      if (v >>> b) &&& 1 == 1 then
        v := v ^^^ (piv[b]!).1
        s := s ^^^ (piv[b]!).2
    out := out.push ((List.range V.size).filter fun i => (s >>> i) &&& 1 == 1)
  return out

meta def matOf (V : Array Nat) (B : Array (List Nat)) (a : Array Nat) : Nat :=
  (List.range 22).foldl (fun acc r =>
    acc ||| (((B[r]!).foldl (fun x i => x ^^^ V[a[i]!]!) 0) <<< (22 * r))) 0

meta def rowsOf (X : Nat) : Array Nat := (Array.range 22).map fun r => (X >>> (22 * r)) &&& m22

meta def enumRecs (V : Array Nat) (G : Array Nat) (cap : Nat) : Array (Array Nat) := Id.run do
  let one := (List.range 22).foldl (fun a i => a ||| (1 <<< (23 * i))) 0
  let code := fun X => vm V[0]! X ||| (vm V[1]! X <<< 22) ||| (vm V[3]! X <<< 44)
  let mut el : Array Nat := #[one]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut pos : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (code one) 0
  let mut tbl : Array (Array Nat) := #[]
  let mut cnt : Array Nat := #[]
  for h in [0:cap] do
    if h < el.size then
      cnt := cnt.push el.size
      let x := el[h]!
      let mut row : Array Nat := #[]
      for j in [0:G.size] do
        let y := mulP x G[j]!
        match pos.get? (code y) with
        | some i => row := row.push i
        | none =>
          pos := pos.insert (code y) el.size
          row := row.push el.size
          el := el.push y
          par := par.push h
          lab := lab.push j
      tbl := tbl.push row
  let n := el.size
  let srt := (Array.range n).qsort fun a b => code el[a]! < code el[b]!
  return (Array.range n).map fun k =>
    rowsOf el[k]! ++ tbl[k]! ++ #[cnt[k]!, par[k]!, lab[k]!, srt[k]!]

end CertificateChecks.KernelSporSch.Co2M.Gen

end
