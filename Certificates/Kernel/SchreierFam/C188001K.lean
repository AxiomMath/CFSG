module

public import Certificates.Kernel.SchreierFam.C188001H
public import Certificates.Kernel.SchreierFam.C188001C1
public import Certificates.Kernel.SchreierFam.C188001C2
public import Certificates.Kernel.SchreierFam.C188001E
public import Certificates.Kernel.SchreierFam.C188001E2
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.U38B

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K

@[expose] noncomputable def PF (k : Nat) : Nat := CertificateChecks.KernelSchreierFam.U38A.F k

@[expose] def idx2 (j : Nat) : Nat := if j < 9 then j else j + 5

@[expose] noncomputable def I : Nat := pidn 513 10

theorem kW : szOK 513 10 = true := by quickRfl

theorem bS1 : allN 14 (fun j => Nat.beq (U38C1.S j) (PF j)) = true := by quickRfl

theorem bS2 : allN 16 (fun j => Nat.beq (U38C2.S j) (PF (idx2 j))) = true := by quickRfl

theorem perm1 : allN 14 (fun j => permOK 513 10 (mask 10) (513 * 10) (U38C1.S j) (U38C1.SI j)) =
    true := by
  quickRfl

theorem perm2 : allN 16 (fun j => permOK 513 10 (mask 10) (513 * 10) (U38C2.S j) (U38C2.SI j)) =
    true := by
  quickRfl

theorem bget1 : ∀ t < 3, base1[t]! = pg 10 (mask 10) U38C1.BP t := by decide +kernel

theorem bget2 : ∀ t < 5, base2[t]! = pg 10 (mask 10) U38C2.BP t := by decide +kernel

theorem orb1 : (List.range 3).map (fun i => rcnt (U38C1.LR i)) = [513, 512, 378] := by
  decide +kernel

theorem hNS1 : 513 ≤ U38C1.NS * 32 := by decide +kernel

theorem hNS2 : 513 ≤ U38C2.NS * 32 := by decide +kernel

theorem pP : allN 7 (fun k => permB 513 10 (PF (Nat.add 25 k))) = true := by quickRfl

@[expose] noncomputable def sift1 (G : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight G (513 * 10)) 0, bAnd(allN 513 (fun t => Nat.blt (pg 10 (mask 10) G t) 513),
    siftK 513 10 (mask 10) (513 * 10) (pidn 513 10) U38C1.LR U38C1.TRI U38C1.BP 3 0 G))

@[expose] noncomputable def sift2 (G : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight G (513 * 10)) 0, bAnd(allN 513 (fun t => Nat.blt (pg 10 (mask 10) G t) 513),
    siftK 513 10 (mask 10) (513 * 10) (pidn 513 10) U38C2.LR U38C2.TRI U38C2.BP 5 0 G))

theorem sifts1 : bAnd(sift1 (PF 25), bAnd(sift1 (PF 30), bAnd(sift1 (PF 31),
    sift1 (U38E1.G 0)))) = true := by
  quickRfl

theorem sifts2 : bAnd(sift2 (PF 27), bAnd(sift2 (U38E2.G 0), sift2 (U38E2.G 1))) = true := by
  quickRfl

theorem pows : bAnd(Nat.beq (pw 513 10 (PF 25) 19) I, bAnd(!Nat.beq (pw 513 10 (PF 25) 1) I,
    bAnd(Nat.beq (pw 513 10 (PF 27) 2) I, bAnd(!Nat.beq (pw 513 10 (PF 27) 1) I,
    bAnd(Nat.beq (pw 513 10 (PF 28) 9) I, bAnd(!Nat.beq (pw 513 10 (PF 28) 3) I,
    bAnd(Nat.beq (pw 513 10 (PF 30) 9) I, bAnd(!Nat.beq (pw 513 10 (PF 30) 3) I,
    bAnd(Nat.beq (pw 513 10 (PF 31) 7) I, !Nat.beq (pw 513 10 (PF 31) 1) I))))))))) = true := by
  quickRfl

theorem fixes : bAnd(Nat.beq (pg 10 (mask 10) (PF 27) 84) 84,
    bAnd(Nat.beq (pg 10 (mask 10) (PF 27) 154) 154, Nat.beq (pg 10 (mask 10) (PF 30) 0) 0)) =
    true := by
  quickRfl

theorem fix7 : ((List.range 513).filter fun p => pg 10 (mask 10) (PF 31) p == p).length = 2 := by
  decide +kernel

theorem n1 : bAnd(Nat.beq U38E1.N 57, bAnd(Nat.beq U38E1.ng 1, Nat.beq (U38E1.G 0) (PF 26))) =
    true := by
  quickRfl

theorem n2 : bAnd(Nat.beq U38E2.N 3024, bAnd(Nat.beq U38E2.ng 2,
    bAnd(Nat.beq (U38E2.G 0) (PF 28), Nat.beq (U38E2.G 1) (PF 29)))) = true := by
  quickRfl

theorem rels1K : relsK 513 10 19 U38C1.BP (PF 25) 3 rels1 = true := by quickRfl

theorem rels2K : relsK 513 10 2 U38C2.BP (PF 27) 5 rels2 = true := by quickRfl

theorem comm1 : commK 513 10 1 (PF 25) U38E1.G = true := by quickRfl

theorem comm2 : commK 513 10 2 (PF 27) U38E2.G = true := by quickRfl

theorem rc : bAnd(Nat.beq (rcnt (U38C1.LR 0)) 513, Nat.beq (rcnt (U38C2.LR 0)) 513) = true := by
  quickRfl

theorem tail1 : allN 513 (ptailBranchK 513 10 U38C1.LR U38C1.TR U38C1.BP (PF 25)
    (pw 513 10 (PF 25)) rels1 U38E1.N U38E1.T 3) = true := by
  quickRfl

end CertificateChecks.KernelSchreierFam.U38B
