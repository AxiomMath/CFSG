module

public import Certificates.Kernel.LocalComp.BfsGen
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public import Lean.Exception

public section

namespace CFSG.KC.Q16Wit

open CFSG.KS.RawGen

meta def keyOf (n : Nat) (ps : List Nat) (a : Array Nat) : Nat :=
  ps.foldr (fun p acc => a[p]! + n * acc) 0

meta def wit (n w : Nat) (pts : Array (Array Nat)) : Array Nat × Array Nat × Array Nat :=
  Id.run do
    let one := pts[0]!
    let mut idx : Std.HashMap Nat Nat := {}
    for i in [0:pts.size] do
      idx := idx.insert (pack w pts[i]!) i
    let mut C := Array.replicate pts.size 0
    let mut W := Array.replicate pts.size 0
    let mut done := Array.replicate pts.size false
    let mut R : Array Nat := #[]
    for i in [0:pts.size] do
      let x := pts[i]!
      let x4 := comp n (comp n x x) (comp n x x)
      if x4 != one && comp n x4 x4 == one && !done[i]! then
        let c := R.size
        R := R.push i
        for j in [0:pts.size] do
          let g := pts[j]!
          match idx.get? (pack w (comp n (inv n g) (comp n x g))) with
          | some k =>
            if !done[k]! then
              done := done.set! k true
              C := C.set! k c
              W := W.set! k j
          | none => pure ()
    return (R, C, W)

meta def keyOrder (n : Nat) (ps : List Nat) (pts : Array (Array Nat)) : Array Nat × Bool :=
  let keys := pts.map (keyOf n ps)
  let order := (Array.range pts.size).qsort fun a b => keys[a]! < keys[b]!
  (order, (List.range (order.size - 1)).all fun k => keys[order[k]!]! < keys[order[k + 1]!]!)

meta def q16Trees (n w : Nat) (gs : List (Array Nat)) (ps : List Nat) : Array (Array Nat) :=
  let (pts, _) := CFSG.KC.BfsGen.search n w gs.toArray
  let (R, C, W) := wit n w pts
  #[(keyOrder n ps pts).1, R, C, W]

meta def q16Step (n w : Nat) (gs : List (Array Nat)) (ps : List Nat) : CFSG.KC.Eval.Step :=
  fun _ => do
    let (pts, _) := CFSG.KC.BfsGen.search n w gs.toArray
    unless (keyOrder n ps pts).2 do throw "two points have the same base key"
    return #[(`nR, .nat (wit n w pts).1.size)]

end CFSG.KC.Q16Wit

end
