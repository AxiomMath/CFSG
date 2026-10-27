module

public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Std.Data.HashMap

public section

namespace CFSG.KC.WordChunks

meta partial def mergeP (s : Array (List Nat)) (a b : List Nat) (i : Nat)
    (out : Array (List Nat)) : Array (List Nat) :=
  if i < s.size then
    if i + 1 < s.size && s[i]! == a && s[i + 1]! == b then mergeP s a b (i + 2) (out.push (a ++ b))
    else mergeP s a b (i + 1) (out.push s[i]!)
  else out

meta def bestPair (seqs : Array (Array (List Nat))) : Option (List Nat × List Nat) := Id.run do
  let mut idx : Std.HashMap (List Nat × List Nat) Nat := {}
  let mut keys : Array (List Nat × List Nat) := #[]
  let mut cnt : Array Nat := #[]
  for s in seqs do
    for i in [1:s.size] do
      let p := (s[i - 1]!, s[i]!)
      match idx[p]? with
      | some k => cnt := cnt.modify k (· + 1)
      | none =>
        idx := idx.insert p keys.size
        keys := keys.push p
        cnt := cnt.push 1
  let mut best : Option (Int × Nat) := none
  for k in [0:keys.size] do
    let g : Int := (cnt[k]! : Int) - ((keys[k]!.1.length + keys[k]!.2.length : Nat) : Int)
    match best with
    | none => best := some (g, k)
    | some (g0, _) => if g > g0 then best := some (g, k)
  match best with
  | some (g, k) => if g > 0 then return some keys[k]! else return none
  | none => return none

meta partial def chunk (seqs : Array (Array (List Nat))) : Array (Array (List Nat)) :=
  match bestPair seqs with
  | some (a, b) => chunk (seqs.map fun s => mergeP s a b 0 #[])
  | none => seqs

open CFSG.KC.Eval in
public meta def chunkVals (ws : Array (List Nat)) : Array (Lean.Name × Val) := Id.run do
  let seqs := chunk (ws.map fun w => (w.map fun x => [x]).toArray)
  let mut idx : Std.HashMap (List Nat) Nat := {}
  let mut dict : Array (List Nat) := #[]
  let mut ixs : Array (List Nat) := #[]
  for s in seqs do
    let mut ik : Array Nat := #[]
    for c in s do
      match idx[c]? with
      | some j => ik := ik.push j
      | none =>
        idx := idx.insert c dict.size
        ik := ik.push dict.size
        dict := dict.push c
    ixs := ixs.push ik.toList
  let enc : List Nat → Val := fun xs => .list (xs.toArray.map fun x => .nat x)
  return #[(`W, .list (dict.map enc)), (`I, .list (ixs.map enc))]

end CFSG.KC.WordChunks
