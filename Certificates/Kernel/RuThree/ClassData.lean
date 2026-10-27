module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
public meta import Std.Data.HashMap
public meta import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib
public import Mathlib

public section

namespace CertificateChecks.KernelRuThree

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native

meta def classDataM : List Nat × List Nat × List Nat := Id.run do
  let pts := ruThreeC0Cert.pts
  let N := pts.size
  let one := idA 4060
  let keyOf := fun (a : Array Nat) => keyA 4060 ruThreeKeys a
  let mut pos : Std.HashMap Nat Nat := {}
  for i in [0:N] do
    pos := pos.insert (keyOf pts[i]!) i
  let gens := ruThreeC0Gens
  let ginv := gens.map (invCand 4060)
  let rel := fun (x : Array Nat) =>
    (eqA 4060 (compA 4060 x x) one ||
      eqA 4060 (CFSG.Monster.B.Mathieu.powArr 4060 x 5) one) && !eqA 4060 x one
  let mut W : Array Nat := Array.replicate N 0
  let mut done : Array Bool := Array.replicate N false
  let mut rsR : Array Nat := #[]
  let mut rsC : Array Nat := #[]
  for i in [0:N] do
    if !done[i]! && rel pts[i]! then
      let t := rsR.size
      let mut qm : Array Nat := #[i]
      let mut qg : Array Nat := #[0]
      done := done.set! i true
      W := W.set! i t
      for h in [0:N] do
        if h < qm.size then
          let m := qm[h]!
          let g := qg[h]!
          for k in [0:gens.size] do
            let m' := pos.getD (keyOf (compA 4060 (compA 4060 gens[k]! pts[m]!) ginv[k]!)) 0
            if !done[m']! then
              let g' := pos.getD (keyOf (compA 4060 pts[g]! ginv[k]!)) 0
              done := done.set! m' true
              W := W.set! m' (256 * g' + t)
              qm := qm.push m'
              qg := qg.push g'
      rsR := rsR.push i
      rsC := rsC.push (N / qm.size)
  return (W.toList, rsR.toList, rsC.toList)

meta def cwM : List Nat := classDataM.1

meta def rrM : List Nat := classDataM.2.1

meta def rcM : List Nat := classDataM.2.2

end CertificateChecks.KernelRuThree

end

#knatlist CertificateChecks.KernelRuThree.CW CertificateChecks.KernelRuThree.cwM
#knatlist CertificateChecks.KernelRuThree.RR CertificateChecks.KernelRuThree.rrM
#knatlist CertificateChecks.KernelRuThree.RC CertificateChecks.KernelRuThree.rcM
