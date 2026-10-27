module

public import Certificates.Kernel.L34W.OutData

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CertificateChecks.KernelL34W

@[expose] def abArr : Array (Array Nat) := #[aST, invTab 42 aST, bST, invTab 42 bST]

@[expose] def sortPair (x y : Nat) : Nat × Nat := if x < y then (x, y) else (y, x)

@[expose] def orbArr : Array (Array Nat) := Id.run do
  let mut recs : Array (Array Nat) := #[#[0, 0, 2, 23]]
  let mut i := 0
  for _ in [0:200] do
    if i < recs.size then
      let r := recs[i]!
      for j in [0:6] do
        let g := gTabs[j]!
        let (a, b) := sortPair g[r[2]!]! g[r[3]!]!
        if !(recs.any fun s => s[2]! == a && s[3]! == b) then
          recs := recs.push #[i, j, a, b]
      i := i + 1
  return recs

@[expose] def packV (a : Array Nat) : Nat := a.foldr (fun v acc => v + 64 * acc) 0

@[expose] def soList : Array Nat :=
  (Array.range 2304).qsort fun x y => packV yArr[x]! < packV yArr[y]!

@[expose] def soArr : Array (Array Nat) := soList.map fun n => #[n]

@[expose] def siArr : Array (Array Nat) :=
  (Array.range 2304).map fun n => #[(soList.findIdx? (· == n)).getD 0]

end CertificateChecks.KernelL34Cov

end
