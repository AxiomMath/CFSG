module

public import Certificates.Kernel.GFR3.J2
public import Certificates.Data.Kernel.Misc.ChainTailOrb
public import Certificates.Kernel.SporSch.Th.GenV4
meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelGFR3.J2.OB

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne

meta def orbL : List Nat × List Nat × List Nat := Id.run do
  let p := ((rawLevels 315 j2ThreeArrs j2ThreeBaseArr)[0]!).pts
  let c := (enumBfs 315 j2ThreeGens j2ThreeBaseArr.toList 1100).pts
  let xs := powPA 3 315 j2ThreeGens[0]!
  let mut idx := Array.replicate 315 0
  for k in [0:p.size] do
    idx := idx.set! (p[k]!) k
  let mut ri := Array.replicate p.size p.size
  let mut ek := Array.replicate p.size 0
  let mut reps : Array Nat := #[]
  for k in [0:p.size] do
    if ri[k]! == p.size && relOK j2ThreeBaseArr xs j2ThreeRels 0 (idA 315) p[k]! then
      let j := reps.size
      reps := reps.push k
      let q := p[k]!
      for e in [0:c.size] do
        let t := idx.getD ((c.getD e #[]).getD q 0) 0
        if ri[t]! == p.size then
          ri := ri.set! t j
          ek := ek.set! t e
  return (reps.toList, (ri.map fun i => if i == p.size then 0 else i).toList, ek.toList)

meta def repL : List Nat := orbL.1
meta def riL : List Nat := orbL.2.1
meta def ekL : List Nat := orbL.2.2

end CertificateChecks.KernelGFR3.J2.OB

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelGFR3.J2.RB CertificateChecks.KernelGFR3.J2.OB.repL
#kss_natlist CertificateChecks.KernelGFR3.J2.RI CertificateChecks.KernelGFR3.J2.OB.riL
#kss_natlist CertificateChecks.KernelGFR3.J2.EK CertificateChecks.KernelGFR3.J2.OB.ekL

namespace CertificateChecks.KernelGFR3.J2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

theorem rep0 : repBranchK 315 9 C.LR C.TR C.BP (E.G 0) (pw 315 9 (E.G 0)) j2ThreeRels E.N E.T 7
    (RB 0) = true := by quickRfl

theorem kOrb : allN 315 (orbRelK 315 9 C.LR C.BP (pw 315 9 (E.G 0)) j2ThreeRels E.N E.T 1 RB RI
    EK) = true := by quickRfl

end CertificateChecks.KernelGFR3.J2

end
