module

public import Certificates.Data.DcHeOverV

public section

namespace CFSG.KD.He589203

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.HeCert
open CFSG.QuasithinUnique.K1.SporadicPerm (slpTabsA)

@[expose] def qp0 : List (Nat × Nat) := [(0, 0)]

partial def lowB (sk : Array Nat) (x lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if sk[mid]! < x then lowB sk x (mid + 1) hi else lowB sk x lo mid
  else lo

@[expose] def rowsOf (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat) :
    Array (List Nat) :=
  let P := B.map (ptsArr G par lab par.size)
  (Array.range par.size).map fun k => P.map fun A => A.getD k 0

@[expose] def sigOf (n : Nat) (rows : Array (List Nat)) : Array Nat :=
  let keys := rows.map (keyNat n 5)
  (Array.range rows.size).qsort fun a b => keys[a]! < keys[b]!

@[expose] def skOf (n : Nat) (rows : Array (List Nat)) : Array Nat :=
  (sigOf n rows).map fun i => keyNat n 5 rows[i]!

@[expose] def cntOf (par : Array Nat) : Array Nat := Id.run do
  let mut b : Array Nat := Array.replicate (par.size + 1) 0
  for j in [1:par.size] do
    b := b.modify par[j]! (· + 1)
  let mut out : Array Nat := #[]
  let mut acc := 1
  for k in [0:par.size] do
    out := out.push acc
    acc := acc + b[k]!
  return out

@[expose] def recOf (n : Nat) (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat)
    (sk : Array Nat) : Array (Array Nat) :=
  let rows := rowsOf B G par lab
  let keys := rows.map (keyNat n 5)
  let M : Std.HashMap Nat Nat := Std.HashMap.ofList ((List.range rows.size).map fun k => (keys[k]!, k))
  let sig := sigOf n rows
  let sinv := invTab sig
  let cnt := cntOf par
  (Array.range rows.size).map fun k =>
    rows[k]!.toArray ++ #[par[k]!, lab[k]!, cnt[k]!, sig[k]!, sinv[k]!, lowB sk keys[k]! 0 sk.size] ++
      ((Array.range G.size).map fun t => M.getD (keyNat n 5 (rows[k]!.map (img (G[t]!)))) 0)

@[expose] def slpA : Array (Array Nat) := slpTabsA hATa hATb hAProg

@[expose] def slpB : Array (Array Nat) := slpTabsA hBTa hBTb hBProg

@[expose] def orbOrder (n : Nat) (G : Array (Array Nat)) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate n false
  let mut out : Array Nat := #[]
  for s in [0:n] do
    if !seen[s]! then
      seen := seen.set! s true
      let mut q : Array Nat := #[s]
      let mut h := 0
      while h < q.size do
        let x := q[h]!
        h := h + 1
        for t in [0:G.size] do
          let y := img (G[t]!) x
          if !seen[y]! then
            seen := seen.set! y true
            q := q.push y
      out := out ++ q
  return out

@[expose] def perms : Array (Array Nat) :=
  let Q := orbOrder 8330 RT
  RT.map invTab ++ #[invTab hATb, invTab hBTb, orbitLabels 8330 RT, Q, invTab Q]

@[expose] def enR : Array Nat × Array Nat := bfsEnumL 8330 B RT 1100

@[expose] def recR : Array (Array Nat) := recOf 8330 B RT enR.1 enR.2 #[]

@[expose] def skR : Array Nat := skOf 8330 (rowsOf B RT enR.1 enR.2)

@[expose] def recVs (D : DcData) : Array (Array (Array Nat)) :=
  let V0 := D.Vs.headD ([], #[], #[], 0)
  let sk0 := skOf D.n (rowsOf D.B (D.VG V0.1) V0.2.1 V0.2.2.1)
  (D.Vs.map fun V => recOf D.n D.B (D.VG V.1) V.2.1 V.2.2.1 sk0).toArray

@[expose] def hposOf (D : DcData) : Array (Array Nat) :=
  let cks := (Array.range D.reps.size).map fun j =>
    (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi j) (D.X j)).toArray
  (Array.range D.NR).map fun k => cks.map fun ks => lowB skR ks[k]! 0 skR.size

@[expose] def ihOf (D : DcData) : Array (Array Nat) :=
  #[(Array.range D.reps.size).map fun j => dcInv D.n D.lb (D.X j),
    (Array.range D.reps.size).map fun j =>
      hitCount D.rSet (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi j) (D.X j))]

@[expose] def ihA : Array (Array Nat) := ihOf heDcA

@[expose] def ihB : Array (Array Nat) := ihOf heDcB

@[expose] def recAV : Array (Array (Array Nat)) := recVs heDcA

@[expose] def recAV0 : Array (Array Nat) := recAV[0]!

@[expose] def recAV1 : Array (Array Nat) := recAV[1]!

@[expose] def recBV : Array (Array (Array Nat)) := recVs heDcB

@[expose] def recBV0 : Array (Array Nat) := recBV[0]!

@[expose] def recBV1 : Array (Array Nat) := recBV[1]!

@[expose] def hposA : Array (Array Nat) := hposOf heDcA

@[expose] def hposB : Array (Array Nat) := hposOf heDcB

end CFSG.KD.He589203

end
