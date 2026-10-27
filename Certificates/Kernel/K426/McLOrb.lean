module

public import Certificates.Kernel.K426.McLChecks
public import Certificates.Data.Kernel.Misc.ChainTailOrb
public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Data.K426McL
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelK426.OB

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer

meta def orbL (S : Array (Array ℕ)) (base : Array ℕ) (x : Array ℕ) (rels : List (ℕ × ℕ × ℕ))
    (c : ArrCert) : List Nat × List Nat × List Nat := Id.run do
  let p := ((rawLevels 275 S base)[0]!).pts
  let c := c.pts
  let xs := powPA 3 275 x
  let mut idx := Array.replicate 275 0
  for k in [0:p.size] do
    idx := idx.set! (p[k]!) k
  let mut ri := Array.replicate p.size p.size
  let mut ek := Array.replicate p.size 0
  let mut reps : Array Nat := #[]
  for k in [0:p.size] do
    if ri[k]! == p.size && relOK base xs rels 0 (idA 275) p[k]! then
      let j := reps.size
      reps := reps.push k
      let q := p[k]!
      for e in [0:c.size] do
        let t := idx.getD ((c.getD e #[]).getD q 0) 0
        if ri[t]! == p.size then
          ri := ri.set! t j
          ek := ek.set! t e
  return (reps.toList, (ri.map fun i => if i == p.size then 0 else i).toList, ek.toList)

meta def orbA : List Nat × List Nat × List Nat :=
  orbL mcl3ChainAArrs mcl3ChainABaseArr mcl3Lines[0]! mcl3RelsA mcl3CACert
meta def orbB : List Nat × List Nat × List Nat :=
  orbL mcl3ChainBArrs mcl3ChainBBaseArr mcl3Lines[1]! mcl3RelsB mcl3CBCert

meta def repAL : List Nat := orbA.1
meta def riAL : List Nat := orbA.2.1
meta def ekAL : List Nat := orbA.2.2
meta def repBL : List Nat := orbB.1
meta def riBL : List Nat := orbB.2.1
meta def ekBL : List Nat := orbB.2.2

end CertificateChecks.KernelK426.OB

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelK426.RBA CertificateChecks.KernelK426.OB.repAL
#kss_natlist CertificateChecks.KernelK426.RIA CertificateChecks.KernelK426.OB.riAL
#kss_natlist CertificateChecks.KernelK426.EKA CertificateChecks.KernelK426.OB.ekAL
#kss_natlist CertificateChecks.KernelK426.RBB CertificateChecks.KernelK426.OB.repBL
#kss_natlist CertificateChecks.KernelK426.RIB CertificateChecks.KernelK426.OB.riBL
#kss_natlist CertificateChecks.KernelK426.EKB CertificateChecks.KernelK426.OB.ekBL

namespace CertificateChecks.KernelK426

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.RankThree.PartTwo.KFacts.K426

@[expose] noncomputable def repA (q : Nat) : Bool :=
  relOKK 9 (mask 9) MA.BP (pw 275 9 (F 4)) mcl3RelsA 0 (pidn 275 9) (rpt 9 (mask 9) (MA.LR 0) q) &&
    ptailBranchIdxK 275 9 MA.LR MA.TR MA.BP (F 4) (pw 275 9 (F 4)) mcl3RelsA EA.N EA.T EA.S 10 q

@[expose] noncomputable def repB (q : Nat) : Bool :=
  relOKK 9 (mask 9) MB.BP (pw 275 9 (F 5)) mcl3RelsB 0 (pidn 275 9) (rpt 9 (mask 9) (MB.LR 0) q) &&
    ptailBranchIdxK 275 9 MB.LR MB.TR MB.BP (F 5) (pw 275 9 (F 5)) mcl3RelsB EB.N EB.T EB.S 10 q

theorem repA0 : repA (RBA 0) = true := by quickRfl

theorem repB0 : repB (RBB 0) = true := by quickRfl

theorem repB1 : repB (RBB 1) = true := by quickRfl

theorem repB2 : repB (RBB 2) = true := by quickRfl

theorem kOrbA : allN 275 (orbRelK 275 9 MA.LR MA.BP (pw 275 9 (F 4)) mcl3RelsA EA.N EA.T 1 RBA
    RIA EKA) = true := by quickRfl

theorem kOrbB : allN 275 (orbRelK 275 9 MB.LR MB.BP (pw 275 9 (F 5)) mcl3RelsB EB.N EB.T 3 RBB
    RIB EKB) = true := by quickRfl

end CertificateChecks.KernelK426

end
