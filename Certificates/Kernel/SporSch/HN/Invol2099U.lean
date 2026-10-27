
module

public import Certificates.Kernel.SporSch.HN.GenF5T
public import Certificates.Kernel.SporSch.HN.Seeds2106K
public import Certificates.Data.Kernel.SporSch.HNF5KronT
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
meta import CFSG.Sporadic.HNSchreier.InvolCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNInvolU

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNSchreier

meta def build : List (Array (Array Nat)) × List (Nat × Nat × Nat) := Id.run do
  let m := mulM 5 133
  let mut M : Array (Array (Array Nat)) := #[rowsA, rowsB]
  let mut sp : Array (Nat × Nat × Nat) := #[(2, 0, 0), (2, 0, 0)]
  let wo := LocalData.outerWord
  let le := fun (l : Nat) => if l = 1 then 0 else 1
  M := M.push (M.getD (le (wo.headD 0)) #[])
  sp := sp.push (1, le (wo.headD 0), 0)
  for l in wo.drop 1 do
    M := M.push (m (M.getD (M.size - 1) #[]) (M.getD (le l) #[]))
    sp := sp.push (0, M.size - 2, le l)
  let U := M.getD 59 #[]
  let Ui := invM 5 133 U
  M := M.push Ui
  sp := sp.push (2, 0, 0)
  M := M.push (m U Ui)
  sp := sp.push (0, 59, 60)
  return (M.toList, sp.toList)

meta def mats : List (Array (Array Nat)) := build.1

meta def spec : List (Nat × Nat × Nat) := build.2

end CertificateChecks.KernelSporSch.HNInvolU

#kss_f5tree CertificateChecks.KernelSporSch.HNIU CertificateChecks.KernelSporSch.HNInvolU.mats
  CertificateChecks.KernelSporSch.HNInvolU.spec

namespace CertificateChecks.KernelSporSch.HNInvolU

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch
open CertificateChecks.KernelSporSch

@[expose] noncomputable def su (k i : Nat) : Nat := slice5 HNIU.MT k i

theorem eqA : allN 133 (fun i => Nat.beq (su 0 i) (HNSeeds.sl 0 i)) = true := by quickRfl
theorem eqB : allN 133 (fun i => Nat.beq (su 1 i) (HNSeeds.sl 1 i)) = true := by quickRfl

theorem blk0 : krBlkT HNIU.MT HNIU.OP HNIU.L HNIU.R 0 11 = true := by quickRfl
theorem blk1 : krBlkT HNIU.MT HNIU.OP HNIU.L HNIU.R 11 10 = true := by quickRfl
theorem blk2 : krBlkT HNIU.MT HNIU.OP HNIU.L HNIU.R 21 10 = true := by quickRfl
theorem blk3 : krBlkT HNIU.MT HNIU.OP HNIU.L HNIU.R 31 10 = true := by quickRfl
theorem blk4 : krBlkT HNIU.MT HNIU.OP HNIU.L HNIU.R 41 10 = true := by quickRfl
theorem blk5 : krBlkT HNIU.MT HNIU.OP HNIU.L HNIU.R 51 11 = true := by quickRfl

theorem specLt : allN 62 (fun k => bAnd(Nat.blt (HNIU.L k) 62, Nat.blt (HNIU.R k) 62)) = true := by
  quickRfl

theorem id61 : allN 133 (fun i => Nat.beq (su 61 i) (idRow5 i)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNInvolU

end
