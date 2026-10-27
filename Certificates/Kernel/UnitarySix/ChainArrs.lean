
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase

public section

namespace CertificateChecks.KernelU6

open CFSG.EvenSmallLie.UnitarySix

@[expose] def invArr (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 693 0
  for i in [0:693] do
    r := r.set! t[i]! i
  return r

@[expose] def wordArr (S : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldr (fun (z : Int) acc =>
    let s := if 0 < z then S[z.toNat - 1]! else invArr S[(-z).toNat - 1]!
    Array.ofFn (n := 693) fun i => s[acc[i.val]!]!) (Array.range 693)

@[expose] def strongArr (gens : Array (Array Nat)) (words : List (List Int)) : Array (Array Nat) :=
  words.foldl (fun S w => S.push (wordArr S w)) gens

@[expose] def lettersArr (ws : List (List Int)) : Array (Array Nat) :=
  (ws.map (wordArr letterArrs)).toArray

@[expose] def aDer : List (List Int) := [[2], [5], [-8, 6, 4, 1]]
@[expose] def kDer : List (List Int) :=
  [[2], [1, 2, -1], [-2, -1, -2, 5, 2, 1], [-2, -1, -2, -3, 5, 3, 2, 1]]
@[expose] def pDer : List (List Int) :=
  [[1], [2], [5], [-1, -3, -8, -11, 6, 4, 11, 1], [10, 11, -10],
    [-2, -16, -11, -10, -11, 17, 11, 10], [-7, -16, -11, -10, -11, -12, 17, 12, 11, 10]]
@[expose] def sDer : List (List Int) := [[2], [5]]
@[expose] def tDer : List (List Int) := [[3]]

@[expose] def aStrong : Array (Array Nat) := strongArr (lettersArr aWords) aDer
@[expose] def kStrong : Array (Array Nat) := strongArr (lettersArr kWords) kDer
@[expose] def pStrong : Array (Array Nat) := strongArr (lettersArr (aWords ++ kWords)) pDer
@[expose] def sStrong : Array (Array Nat) := strongArr (lettersArr (aWords ++ tWords)) sDer
@[expose] def tStrong : Array (Array Nat) := strongArr (lettersArr tWords) tDer

@[expose] def aBase : Array Nat := #[1, 3, 45]
@[expose] def kBase : Array Nat := #[0, 1, 3]
@[expose] def pBase : Array Nat := #[0, 1, 3, 45]
@[expose] def tBase : Array Nat := #[1, 3]

end CertificateChecks.KernelU6

end
