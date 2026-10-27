module

public import Certificates.Kernel.K426.McLText
public import Certificates.Kernel.K426.McLChains
public import Certificates.Kernel.K426.McLEnum
public import Certificates.Kernel.K426.McLEnumA
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.K426K
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true

namespace CertificateChecks.KernelK426

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.RankThree.PartTwo.KFacts.K426
open CertificateChecks.KernelCensus

@[expose] noncomputable def F (j : Nat) : Nat := McLKT.F j

theorem szOK' : szOK 275 9 = true := by quickRfl

theorem permF : allN 339 (fun j => permB 275 9 (F j)) = true := by quickRfl

theorem nums : Nat.beq EQ.N 729 = true ∧ Nat.beq EQ.ng 4 = true ∧ Nat.beq EA.N 29160 = true ∧
    Nat.beq EA.ng 3 = true ∧ Nat.beq EO.N 243 = true ∧ Nat.beq EO.ng 5 = true ∧
    Nat.beq EB.N 972 = true ∧ Nat.beq EB.ng 3 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl⟩

theorem gens : allN 4 (fun j => Nat.beq (EQ.G j) (F (0 + j))) = true ∧
    allN 3 (fun j => Nat.beq (EA.G j) (F (316 + j))) = true ∧
    allN 5 (fun j => Nat.beq (EO.G j) (F (319 + j))) = true ∧
    allN 3 (fun j => Nat.beq (EB.G j) (F (336 + j))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem chains : allN 16 (fun j => Nat.beq (MA.S j) (F (300 + j))) = true ∧
    allN 12 (fun j => Nat.beq (MB.S j) (F (324 + j))) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem heads : Nat.beq (MA.S 0) (McLS.F 0) = true ∧ Nat.beq (MA.S 1) (McLS.F 1) = true ∧
    Nat.beq (MB.S 0) (McLS.F 0) = true ∧ Nat.beq (MB.S 1) (McLS.F 1) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem permA : allN 16 (fun j => permOK 275 9 (mask 9) (275 * 9) (MA.S j) (MA.SI j)) = true := by
  quickRfl

theorem permB' : allN 12 (fun j => permOK 275 9 (mask 9) (275 * 9) (MB.S j) (MB.SI j)) = true := by
  quickRfl

theorem bgetA : ∀ t < 10, mcl3ChainABaseArr[t]! = pg 9 (mask 9) MA.BP t := by decide +kernel

theorem bgetB : ∀ t < 10, mcl3ChainBBaseArr[t]! = pg 9 (mask 9) MB.BP t := by decide +kernel

theorem lines : linesK 275 9 3 EQ.N 148 EQ.T (fun j => F (4 + j)) = true := by quickRfl

theorem trans : transK 275 9 148 (fun j => F (152 + j)) (fun j => F (4 + j)) (fun j => F (4 + j))
    mcl3Rec = true := by quickRfl

theorem siftQ : allN 4 (fun k => siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (F (0 + k))) = true := by
  quickRfl

theorem siftH : allN 148 (fun k => siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (F (152 + k))) =
    true := by quickRfl

theorem siftO : allN 5 (fun k => siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (F (319 + k))) = true := by
  quickRfl

theorem siftCA : allN 3 (fun k => siftOK 275 9 10 MA.LR MA.TRI MA.BP (F (316 + k))) = true := by
  quickRfl

theorem siftCB : allN 3 (fun k => siftOK 275 9 10 MB.LR MB.TRI MB.BP (F (336 + k))) = true := by
  quickRfl

theorem relsA : relsK 275 9 3 MA.BP (F 4) 10 mcl3RelsA = true := by quickRfl

theorem relsB : relsK 275 9 3 MB.BP (F 5) 10 mcl3RelsB = true := by quickRfl

theorem commA : commK 275 9 3 (F 4) (fun j => F (316 + j)) = true := by quickRfl

theorem commB : commK 275 9 3 (F 5) (fun j => F (336 + j)) = true := by quickRfl

theorem rc : Nat.beq (rcnt (MA.LR 0)) 275 = true ∧ Nat.beq (rcnt (MB.LR 0)) 275 = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem normal : normalK 275 9 3 EA.N EO.N 3 5 EA.T EA.S EO.T EO.S (fun j => F (316 + j))
    (fun j => F (319 + j)) = true := by quickRfl

end CertificateChecks.KernelK426

end
