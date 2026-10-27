module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.StdOdd.SlpCmd
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.StdOdd.SlpCmd

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.Eval CFSG.KC.Misc.E6Std

public meta def valNat : Val → Except String Nat
  | .nat n => pure n
  | _ => throw "candStep: expected a number"

public meta def valNats : Val → Except String (Array Nat)
  | .list xs => xs.mapM valNat
  | _ => throw "candStep: expected a list"

public meta partial def segsT (l : List Nat) : List (List Nat) :=
  match l with
  | [] => []
  | n :: t => t.take n :: segsT (t.drop n)

public meta def rowXT (r : Nat) (U : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for d in [0:U.size] do
    if (r >>> d) &&& 1 == 1 then acc := acc ^^^ U[d]!
  return acc

public meta def stepT (Ms ms : Array Nat) (U : Array Nat) : Array Nat := Id.run do
  let o := ms.foldl (· ||| ·) 0
  let mut V : Array Nat := #[]
  for c in [0:156] do
    let x := U[c]!
    let mut y := x ^^^ (x &&& o)
    for l in [0:Ms.size] do
      y := y ^^^ (ms[l]! &&& rowXT (Ms[l]! >>> (156 * c)) U)
    V := V.push y
  return V

public meta def candStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 8 then throw "candStep: expected 8 arguments"
  let V ← valNats args[0]!
  let CP ← valNat args[1]!
  let HW ← valNat args[2]!
  let hl ← valNats args[3]!
  let cm ← valNats args[4]!
  let p ← valNat args[5]!
  let g ← valNat args[6]!
  let wc ← valNat args[7]!
  let s := cm[0]!
  let hD := cm[1]!
  let A := V[0]!
  let B := V[1]!
  let mut X := oneBT ()
  let mut w := wc
  while w > 0 do
    let d := w % 4
    X := mulBT X (if d == 1 then A else if d == 2 then B else mulBT B B)
    w := w / 4
  let mut P := oneBT ()
  for _ in [0:p - 1] do
    P := mulBT P X
  let lines := segsT hl.toList
  let Ms := #[P] ++ (lines.map fun line => line.foldl (fun acc i => mulBT acc V[i]!) (oneBT ())).toArray
  let nh := Ms.size
  let bw := (s + 7) / 8
  let F := (1 <<< s) - 1
  let mut U : Array Nat := (Array.range 156).map fun c => (CP >>> (8 * bw * c)) &&& F
  let mut CC := 0
  let mut j := 0
  for t in [0:hD] do
    if g > 0 && t > 0 && t % g == 0 then
      for c in [0:156] do
        CC := CC ||| (U[c]! <<< (8 * bw * (156 * j + c)))
      j := j + 1
    let ms := (Array.range nh).map fun l => (HW >>> (8 * bw * (nh * t + l))) &&& F
    U := stepT Ms ms U
  return #[(`CC, .nat CC)]

end CFSG.KD.StdOdd.Cent
