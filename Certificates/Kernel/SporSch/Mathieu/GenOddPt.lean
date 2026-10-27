module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.OddPtSound
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Ru.RowsGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound

public section

namespace CFSG.KS.SporSch.OddPtG

open CFSG.KS.SporSch.MOCG

meta def cycLen (f : Nat → Nat) (p bound : Nat) : Nat := Id.run do
  let mut q := f p
  let mut c := 1
  while q != p && c ≤ bound do
    q := f q
    c := c + 1
  return c

meta def badPt (f : Nat → Nat) (n mo : Nat) : Option (Nat × Nat) := Id.run do
  for p in [0:n] do
    let c := cycLen f p n
    if mo % c != 0 then return some (p, c)
  return none

meta def oddCodes (n mo L : Nat) (S : Array (Array Nat)) (base : Array Nat) :
    Array (Array Nat) := Id.run do
  let E := prods (levelsOf n S base) 0 (idA n)
  let N := E.size
  let NB := (N + L - 1) / L
  let idn := idA n
  let Ei := E.map invA
  let lenC := fun (c : Nat) => if c < 256 then c else 0
  let codes := (Array.range N).map fun j => Id.run do
    let x := E[j]!
    if x == idn then return 0
    match badPt (fun q => x[q]!) n mo with
    | some (p, c) => return 1 + 4 * (lenC c + 256 * p)
    | none =>
      for hi in [0:N] do
        let h := E[hi]!
        let hv := Ei[hi]!
        match badPt (fun q => x[h[x[hv[q]!]!]!]!) n mo with
        | some (p, c) => return 2 + 4 * (lenC c + 256 * (p + 65536 * hi))
        | none => pure ()
      return 0
  return (Array.range (NB * L)).map fun j => #[codes[j % N]!]

end CFSG.KS.SporSch.OddPtG

end
