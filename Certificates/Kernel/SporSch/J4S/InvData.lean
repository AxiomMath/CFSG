module

public import CFSG.Sporadic.Schreier.J4SInvData

public section

namespace CertificateChecks.KernelSporSch.J4Inv

open CFSG.Sporadic.J4Schreier

@[expose] def wordOn (s : List Int) (P : Pair) : Pair :=
  s.foldr (fun l acc => mulP (letterP Xn Yn l) acc) P

@[expose] def sufs (w : List Int) (N : Nat) : Array Pair :=
  ((List.range N).foldr (fun k acc => wordOn ((w.drop (100 * k)).take 100) (acc.headD oneP) :: acc)
    [oneP]).toArray

@[expose] def nSeg (g : Nat) : Nat := ((fiveGenWords[g]!).length + 99) / 100

@[expose] def kSuf0 : Array Pair := sufs fiveGenWords[0]! (nSeg 0)
@[expose] def kSuf1 : Array Pair := sufs fiveGenWords[1]! (nSeg 1)
@[expose] def kSuf2 : Array Pair := sufs fiveGenWords[2]! (nSeg 2)
@[expose] def kSuf3 : Array Pair := sufs fiveGenWords[3]! (nSeg 3)

@[expose] def forestW : Array (Array Nat) := Id.run do
  let mut a := Array.replicate 1024 (Array.replicate 2048 0)
  for j in [0:19967] do
    a := a.modify (fE j) (·.set! (fN j) j)
  return a

end CertificateChecks.KernelSporSch.J4Inv

end
