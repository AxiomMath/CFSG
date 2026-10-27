module

public import Certificates.Kernel.HS589207.Q

public section

namespace CFSG.KD.HS589206.E16

open CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative
  CFSG.Quasithin.H13.LocDbl.DcRank CFSG.KD.HS589207

@[expose] def recOf (G : Array (Array Nat)) (cap N : Nat) : Array (Array Nat) :=
  let en := bfsEnumL 100 B100 G cap
  let rows := (enumTabs G en N).map Array.toList
  let keys := rows.map (keyNat 100 100)
  let H : Std.HashMap Nat Nat :=
    Std.HashMap.ofList ((List.range rows.size).map fun k => (keys[k]!, k))
  let so := sigOf keys
  let cnt := cntOf en.1
  (Array.range rows.size).map fun k =>
    rows[k]!.toArray ++ #[en.1[k]!, en.2[k]!, cnt[k]!, so.1[k]!, so.2[k]!, 0] ++
      ((Array.range G.size).map fun t => H.getD (keyNat 100 100 (rows[k]!.map (img (G[t]!)))) 0)

@[expose] def recS : Array (Array Nat) := recOf sTabs 600 512

@[expose] def recS5 : Array (Array Nat) := recOf s5Tabs 200 125

@[expose] def sInv : Array Nat :=
  ((List.range 512).filter fun k => isInvT 100 (sElems.getD k #[])).toArray

@[expose] def tabs : Array (Array Nat) := sTabs ++ s5Tabs ++ #[sInv]

@[expose] def iTab (i : Nat) : Array Nat := sElems.getD (sInv.getD i 0) #[]

@[expose] def pairRow (i : Nat) : Array Nat :=
  (Array.range sInv.size).map fun j =>
    if i == j then 0
    else if commT (iTab i) (iTab j) then
      1 + ((List.range sInv.size).find? fun c => iTab c == compT (iTab i) (iTab j)).getD 0
    else
      128 + ((List.range 100).find? fun q =>
        img (iTab i) (img (iTab j) q) != img (iTab j) (img (iTab i) q)).getD 0

@[expose] def pairs : Array (Array Nat) := (Array.range sInv.size).map pairRow

@[expose] def pe0 (a b : Nat) : Nat := (pairs.getD a #[]).getD b 0

@[expose] def cm0 (a b : Nat) : Bool := 0 < pe0 a b && pe0 a b < 128

@[expose] def mul0 (a b : Nat) : Nat := pe0 a b - 1

@[expose] def qEl0 (i j k l : Nat) : Option (List Nat) :=
  let ij := mul0 i j
  let ik := mul0 i k
  let jk := mul0 j k
  let ijk := mul0 ij k
  if cm0 ij k && cm0 ij l && cm0 ik l && cm0 jk l && cm0 ijk l then
    some [i, j, k, l, ij, ik, mul0 i l, jk, mul0 j l, mul0 k l, ijk, mul0 ij l, mul0 ik l,
      mul0 jk l, mul0 ijk l]
  else none

@[expose] def masks : Array Nat := Id.run do
  let n := sInv.size
  let mut out : Array Nat := #[]
  for i in [0:n] do
    for j in [i + 1:n] do
      if cm0 i j then
        for k in [j + 1:n] do
          if cm0 i k && cm0 j k then
            for l in [k + 1:n] do
              if cm0 i l && cm0 j l && cm0 k l then
                match qEl0 i j k l with
                | some xs =>
                  let m := xs.foldl (fun a x => a + 2 ^ x) 0
                  if xs.eraseDups.length == 15 && !out.contains m then out := out.push m
                | none => pure ()
  return out

@[expose] def maskRows : Array (Array Nat) :=
  masks.map fun m => (Array.range 7).map fun t => (m >>> (14 * t)) % 16384

end CFSG.KD.HS589206.E16

end
