module

public import Certificates.Kernel.B3S3.GenL
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.SmallSpor.Sp6Inputs
public meta import Certificates.Kernel.SmallSpor.Sp6Inputs
public meta import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
public meta import CFSG.Monster.B.Mathieu.Order
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CertificateChecks.KernelSmallSpor.Sp6S

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier

meta def img (g : Equiv.Perm (Fin 36)) : Array Nat := (CFSG.Monster.B.Mathieu.imageList g).toArray

meta def sG1 : Array (Array Nat) := (sWords1.map fun wd => img (evalCodes sp6CentGens1 wd)).toArray

meta def sG2 : Array (Array Nat) := (sWords2.map fun wd => img (evalCodes sp6CentGens2 wd)).toArray

meta def sG3 : Array (Array Nat) := (sWords3.map fun wd => img (evalCodes sp6CentGens3 wd)).toArray

meta def sG4 : Array (Array Nat) := (sWords4.map fun wd => img (evalCodes sp6CentGens4 wd)).toArray

meta def wit (gs : Array (Array Nat)) (r : Equiv.Perm (Fin 36)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 36 6 gs).1
  let ra := img r
  let cmp := CFSG.KS.RawGen.comp 36
  let inv := fun (g : Array Nat) => Array.ofFn (n := 36) fun i => (g.toList.idxOf i.val)
  let one := Array.ofFn (n := 36) fun i => i.val
  (List.range pts.size).map fun i =>
    let c := pts[i]!
    if cmp c c == ra then
      ((List.range pts.size).find? fun j =>
        let g := pts[j]!
        let x := cmp c (cmp (cmp g c) (inv g))
        cmp x x == one && x != one && x != ra).getD 0
    else 0

meta def w1 : List Nat := wit sG1 sp6Rep1

meta def w2 : List Nat := wit sG2 sp6Rep2

meta def w3 : List Nat := wit sG3 sp6Rep3

meta def w4 : List Nat := wit sG4 sp6Rep4

end CertificateChecks.KernelSmallSpor.Sp6S

end

set_option maxRecDepth 400000

#kb3_enum_l CertificateChecks.KernelSmallSpor.Sp6S.E1 CertificateChecks.KernelSmallSpor.Sp6S.sG1
  CertificateChecks.KernelSmallSpor.Sp6S.base1 36 6
#kb3_enum_l CertificateChecks.KernelSmallSpor.Sp6S.E2 CertificateChecks.KernelSmallSpor.Sp6S.sG2
  CertificateChecks.KernelSmallSpor.Sp6S.base2 36 6
#kb3_enum_l CertificateChecks.KernelSmallSpor.Sp6S.E3 CertificateChecks.KernelSmallSpor.Sp6S.sG3
  CertificateChecks.KernelSmallSpor.Sp6S.base3 36 6
#kb3_enum_l CertificateChecks.KernelSmallSpor.Sp6S.E4 CertificateChecks.KernelSmallSpor.Sp6S.sG4
  CertificateChecks.KernelSmallSpor.Sp6S.base3 36 6
#kss_natlist CertificateChecks.KernelSmallSpor.Sp6S.W1 CertificateChecks.KernelSmallSpor.Sp6S.w1
#kss_natlist CertificateChecks.KernelSmallSpor.Sp6S.W2 CertificateChecks.KernelSmallSpor.Sp6S.w2
#kss_natlist CertificateChecks.KernelSmallSpor.Sp6S.W3 CertificateChecks.KernelSmallSpor.Sp6S.w3
#kss_natlist CertificateChecks.KernelSmallSpor.Sp6S.W4 CertificateChecks.KernelSmallSpor.Sp6S.w4
