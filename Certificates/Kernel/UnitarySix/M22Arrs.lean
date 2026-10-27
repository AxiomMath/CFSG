module

public import Certificates.Kernel.LocalComp.M22Tables

public section

namespace CertificateChecks.KernelU6

@[expose] def invArr22 (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 22 0
  for i in [0:22] do
    r := r.set! t[i]! i
  return r

@[expose] def wordArr22 (S : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldr (fun (z : Int) acc =>
    let s := if 0 < z then S[z.toNat - 1]! else invArr22 S[(-z).toNat - 1]!
    Array.ofFn (n := 22) fun i => s[acc[i.val]!]!) (Array.range 22)

@[expose] def m22Der : List (List Int) :=
  [[-1, 2, -1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2,
      1, 1],
    [-1, -2, -2, -3, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1,
      1, 2, 1, 2],
    [-1, -2, -2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 2,
      1, 1, 2],
    [-4, -1, -2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1,
      2, 2, 1],
    [-3, 4, -3, -1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 1, 1,
      2, 1, 2, 1, 2],
    [-7, -6, -6, -3, 4, -1, -4, -2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1,
      2, 1, 2, 2, 1, 1, 1, 1, 1],
    [7, -6, -4, -1, -8, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1,
      1, 2, 1, 1, 2],
    [-6, 8, -1, -8, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
      2, 1, 1, 2],
    [8, -9, -5, 7, -4, 8, -2, -9, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1,
      2, 2, 1, 2, 1, 2, 2, 2]]

@[expose] def m22Strong : Array (Array Nat) :=
  m22Der.foldl (fun S w => S.push (wordArr22 S w)) #[CertificateChecks.KernelLC.m22TA, CertificateChecks.KernelLC.m22TB]

@[expose] def m22Base : Array Nat := #[0, 1, 2, 3, 4]

end CertificateChecks.KernelU6

end
