module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

namespace CFSG.KC.Misc.HexWords

open CFSG.KS.RawGen

public meta def tables (s : String) (d n N : Nat) : Array (Array Nat) :=
  let b := s.toUTF8
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  Array.ofFn (n := N) fun j => Array.ofFn (n := n) fun i =>
    (List.range d).foldl (fun a t => a * 16 + hv (b.get! (d * (n * j.val + i.val) + t))) 0

public meta def invs (s : String) (d n w N : Nat) : Array Nat :=
  (tables s d n N).map fun t => pack w (inv n t)

public meta def words (s : String) (d n w N : Nat) (wds : List String) : Array Nat :=
  let T := tables s d n N
  wds.toArray.map fun wd => Id.run do
    let ts := (wd.splitOn " ").filter (· ≠ "") |>.map String.toNat!
    let mut acc : Array Nat := Array.ofFn (n := n) fun i => i.val
    for t in ts.reverse do
      acc := comp n T[t]! acc
    return pack w acc

end CFSG.KC.Misc.HexWords
