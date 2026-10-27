module

public section

namespace CFSG.KC.StdOdd.Orbit

meta def benesDs (m : Nat) : List Nat :=
  (List.range m).map (fun t => 1 <<< (m - 1 - t)) ++
    (List.range (m - 1)).map (fun t => 1 <<< (t + 1))

meta def setBitB (b : ByteArray) (p : Nat) : ByteArray :=
  b.set! (p >>> 3) (b.get! (p >>> 3) ||| ((1 : UInt8) <<< (p &&& 7).toUInt8))

meta def routeBenes (m : Nat) (dst : Array Nat) : Array ByteArray := Id.run do
  let W := 1 <<< m
  let zero : ByteArray := ⟨Array.replicate ((W + 7) / 8) 0⟩
  let mut masks : Array ByteArray := Array.replicate (2 * m - 1) zero
  let mut f := dst
  let mut finv : Array Nat := Array.replicate W 0
  for q in [0:W] do
    finv := finv.set! f[q]! q
  for lvl in [0:m - 1] do
    let h := 1 <<< (m - 1 - lvl)
    let lowH := h - 1
    let hiMask := (W - 1) ^^^ (2 * h - 1)
    let mut col : ByteArray := ⟨Array.replicate W 2⟩
    for q0 in [0:W] do
      if col.get! q0 == 2 then
        let mut q := q0
        let mut go := true
        while go do
          col := col.set! q 0
          let q2 := finv[f[q]! ^^^ h]!
          col := col.set! q2 1
          let q3 := q2 ^^^ h
          if col.get! q3 == 2 then q := q3 else go := false
    let mut mi := masks[lvl]!
    let mut mo := masks[2 * m - 2 - lvl]!
    masks := masks.set! lvl zero
    masks := masks.set! (2 * m - 2 - lvl) zero
    let mut nf : Array Nat := Array.replicate W 0
    let mut nfi : Array Nat := Array.replicate W 0
    for q in [0:W] do
      let c := col.get! q
      if q &&& h == 0 then
        if c == 1 then mi := setBitB mi q
        if col.get! finv[q]! == 1 then mo := setBitB mo q
      let base := (q &&& hiMask) + (if c == 1 then h else 0)
      let p := base + (q &&& lowH)
      let d := base + (f[q]! &&& lowH)
      nf := nf.set! p d
      nfi := nfi.set! d p
    masks := masks.set! lvl mi
    masks := masks.set! (2 * m - 2 - lvl) mo
    f := nf
    finv := nfi
  let mut mid := masks[m - 1]!
  masks := masks.set! (m - 1) zero
  for p in [0:W / 2] do
    if f[2 * p]! != 2 * p then mid := setBitB mid (2 * p)
  masks := masks.set! (m - 1) mid
  return masks

meta def dswT (d m x : Nat) : Nat :=
  let t := ((x >>> d) ^^^ x) &&& m
  x ^^^ (t ^^^ (t <<< d))

meta def netT (ds ms : List Nat) (x : Nat) : Nat :=
  (ds.zip ms).foldl (fun x dm => dswT dm.1 dm.2 x) x

meta def netRevT (ds ms : List Nat) (x : Nat) : Nat :=
  (ds.zip ms).foldr (fun dm x => dswT dm.1 dm.2 x) x

meta partial def natOfWords (w : Array UInt64) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then w[lo]!.toNat
  else
    let mid := lo + (hi - lo) / 2
    natOfWords w lo mid ||| (natOfWords w mid hi <<< (64 * (mid - lo)))

meta partial def natOfBytes (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi ≤ lo + 8 then Id.run do
    let mut acc := 0
    for k in [0:hi - lo] do
      acc := acc ||| ((b.get! (lo + k)).toNat <<< (8 * k))
    return acc
  else
    let mid := lo + (hi - lo) / 2
    natOfBytes b lo mid ||| (natOfBytes b mid hi <<< (8 * (mid - lo)))

meta def transpose64 (a : Array UInt64) : Array UInt64 := Id.run do
  let mut a := a
  let mut j : Nat := 32
  let mut m : UInt64 := 0x00000000FFFFFFFF
  while j != 0 do
    for t in [0:64] do
      if t &&& j == 0 then
        let x := a[t]!
        let y := a[t + j]!
        let tmp := ((x >>> j.toUInt64) ^^^ y) &&& m
        a := a.set! t (x ^^^ (tmp <<< j.toUInt64))
        a := a.set! (t + j) (y ^^^ tmp)
    j := j / 2
    m := m ^^^ (m <<< j.toUInt64)
  return a

meta def planeOfBit (j : Nat) : Nat := if j < 78 then 2 * j else 2 * (j - 78) + 1

meta def planesOf (keys : Array Nat) (n : Nat) : Array Nat := Id.run do
  let nb := (n + 63) / 64
  let mut words : Array (Array UInt64) := Array.replicate 156 (Array.replicate nb 0)
  for b in [0:nb] do
    for jw in [0:3] do
      let mut a : Array UInt64 := Array.replicate 64 0
      for t in [0:64] do
        let p := 64 * b + t
        if p < n then
          a := a.set! t (((keys[p]! >>> (64 * jw)) &&& 0xFFFFFFFFFFFFFFFF).toUInt64)
      a := transpose64 a
      for k in [0:64] do
        let j := 64 * jw + k
        if j < 156 then
          words := words.modify (planeOfBit j) (·.set! b a[k]!)
  return words.map fun w => natOfWords w 0 w.size

meta def sortedKeys (pts : Array (Nat × Nat)) : Array Nat :=
  (pts.map fun v => v.1 + (v.2 <<< 78)).qsort (· < ·)

meta def ranksOf (keys : Array Nat) (idx : Nat × Nat → Nat) : Array Nat := Id.run do
  let mut rank : Array Nat := Array.replicate keys.size 0
  for p in [0:keys.size] do
    let u := keys[p]!
    rank := rank.set! (idx (u &&& ((1 <<< 78) - 1), u >>> 78)) p
  return rank

meta def movesOf (W : Nat) (rank nb : Array Nat) : Array Nat := Id.run do
  let mut d : Array Nat := Array.range W
  for i in [0:rank.size] do
    d := d.set! rank[i]! rank[nb[i]!]!
  return d

meta def bytesToNats (bs : Array ByteArray) : List Nat :=
  bs.toList.map fun b => natOfBytes b 0 b.size

meta def reachSets (ds MA MB : List Nat) (r n : Nat) : Option (Array Nat) := Id.run do
  let fullN := (1 <<< n) - 1
  let mut R := 1 <<< r
  let mut RS : Array Nat := #[R]
  let mut ok := true
  while ok && R != fullN do
    let R' := (R ||| netT ds MA R) ||| (netT ds MB R ||| netRevT ds MB R)
    if R' == R then ok := false
    R := R'
    RS := RS.push R
  return if ok then some RS else none

end CFSG.KC.StdOdd.Orbit

end
