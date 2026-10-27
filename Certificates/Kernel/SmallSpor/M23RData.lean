module

public import Certificates.Kernel.SmallSpor.M23Data
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Kernel.SmallSpor.M23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Monster.B.Mathieu.Order
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.LocalComp.BfsGen

public section

namespace CertificateChecks.KernelSmallSpor.M23

meta def witK : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 23 5 kG).1
  let ra := (CFSG.Monster.B.Mathieu.imageList
    (CFSG.Sporadic.Schreier.m23InvReps.getD 0 1)).toArray
  let cmp := CFSG.KS.RawGen.comp 23
  let inv := fun (g : Array Nat) => Array.ofFn (n := 23) fun i => (g.toList.idxOf i.val)
  let one := Array.ofFn (n := 23) fun i => i.val
  (List.range pts.size).map fun i =>
    let c := pts[i]!
    if cmp c c == ra then
      ((List.range pts.size).find? fun j =>
        let g := pts[j]!
        let x := cmp c (cmp (cmp g c) (inv g))
        cmp x x == one && x != one && x != ra).getD 0
    else 0

end CertificateChecks.KernelSmallSpor.M23

end

#kss_natlist CertificateChecks.KernelSmallSpor.M23.WK CertificateChecks.KernelSmallSpor.M23.witK
