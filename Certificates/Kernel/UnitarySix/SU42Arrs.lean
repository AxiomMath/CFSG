module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Data

public section

namespace CertificateChecks.KernelU6

open CFSG.EvenSmallLie.UnitarySix.YamadaPar (genBits bmulVec)

@[expose] def su42TA : Array Nat := Array.ofFn (n := 256) fun p => bmulVec 8 8 (genBits 0) p.val

@[expose] def su42TB : Array Nat := Array.ofFn (n := 256) fun p => bmulVec 8 8 (genBits 1) p.val

@[expose] def invArr256 (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 256 0
  for i in [0:256] do
    r := r.set! t[i]! i
  return r

@[expose] def wordArr256 (S : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldr (fun (z : Int) acc =>
    let s := if 0 < z then S[z.toNat - 1]! else invArr256 S[(-z).toNat - 1]!
    Array.ofFn (n := 256) fun i => s[acc[i.val]!]!) (Array.range 256)

@[expose] def su42Der : List (List Int) :=
  [[-1, 2, -1, -2, -1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2,
      2, 2, 1, 1, 2],
    [-2, -2, -1, -2, -1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2,
      1, 1, 2, 1, 1],
    [2, -3, 2, -1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1,
      1, 1, 2],
    [-5, 2, -5, 2, -5, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2,
      2, 1, 1, 1],
    [-3, -4, -1, -2, -2, -1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2,
      2, 2, 2, 1, 1, 2],
    [-3, -4, -5, -2, -5, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1,
      1, 2, 1, 2, 1, 1],
    [-6, -3, -4, -1, -2, -1, -3, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1,
      2, 2, 2, 1, 1, 2, 2, 1]]

@[expose] def su42Strong : Array (Array Nat) :=
  su42Der.foldl (fun S w => S.push (wordArr256 S w)) #[su42TA, su42TB]

@[expose] def su42Base : Array Nat := #[1, 4, 16, 64]

end CertificateChecks.KernelU6
