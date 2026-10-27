module

public import Certificates.Kernel.HS589206.E16Q

public section

namespace CFSG.KD.HS589206.E16

open CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative

@[expose] def maskBits (m : Nat) : List Nat := (List.range sInv.size).filter fun i => (m >>> i) % 2 == 1

@[expose] def eFix (m : Nat) : List Nat :=
  (List.range 100).filter fun q => (maskBits m).all fun i => img (iTab i) q == q

@[expose] def orbitPts (m q : Nat) : List Nat :=
  (q :: (maskBits m).map fun i => img (iTab i) q).eraseDups

@[expose] def wordTo (tgt : List Nat) : List Nat := Id.run do
  let mut seen : Std.HashMap (List Nat) (List Nat) := (∅ : Std.HashMap (List Nat) (List Nat)).insert F0 []
  let mut queue : Array (List Nat) := #[F0]
  let mut i := 0
  for _ in [0:4000] do
    if h : i < queue.size then
      let s := queue[i]
      i := i + 1
      for l in [0:4] do
        let s' := (s.map (img (AB.getD l #[]))).mergeSort
        if !seen.contains s' then
          seen := seen.insert s' (l :: seen.getD s [])
          queue := queue.push s'
  return seen.getD tgt []

@[expose] def blocks (m : Nat) : List Nat :=
  ((List.range 100).filter fun q => (orbitPts m q).length == 2).foldl
    (fun acc q => if acc.contains q then acc else acc ++ orbitPts m q) []

@[expose] def wit (m q : Nat) : List Nat :=
  let B := maskBits m
  match B.find? (fun i => img (iTab i) q != q) with
  | none => [0, 0]
  | some a =>
    [a, (B.find? fun c => img (iTab c) q != q && img (iTab c) q != img (iTab a) q).getD 0]

@[expose] def eRow (m : Nat) : Array Nat :=
  let F := eFix m
  if F.length == 8 then
    let w := wordTo F
    #[0, w.length] ++ w.toArray
  else
    let T := blocks m
    #[1] ++ T.toArray ++
      ((List.range 100).flatMap fun q => if T.contains q then [0, 0] else wit m q).toArray

@[expose] def eRows : Array (Array Nat) := masks.map eRow

end CFSG.KD.HS589206.E16

end
