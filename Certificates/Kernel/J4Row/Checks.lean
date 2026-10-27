module

public import Certificates.Data.Kernel.J4Row.Chk
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Kernel.J4Row.Data
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Row

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.J4Row CFSG.KD.J4Row
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (starMasks)

@[expose] noncomputable def us : List Nat :=
  [CFSG.KD.J4Q.U0, CFSG.KD.J4Q.U1, CFSG.KD.J4Q.U2, CFSG.KD.J4Q.U3, CFSG.KD.J4Q.U4, CFSG.KD.J4Q.U5,
    CFSG.KD.J4Q.U6, CFSG.KD.J4Q.U7, CFSG.KD.J4Q.U8, CFSG.KD.J4Q.U9, CFSG.KD.J4Q.U10]

@[expose] noncomputable def chk (prog : List (Nat × Nat × Nat)) (p m n rz ru : Nat)
    (gens cols : List Nat) (bfs : List (Nat × Nat)) (N : Nat) : Bool :=
  rowChkK CFSG.KD.J4Q.c CFSG.KD.J4Q.rm CFSG.KD.J4Q.one us CFSG.KD.J4Q.A CFSG.KD.J4Q.Ai
    CFSG.KD.J4Q.B CFSG.KD.J4Q.Bi prog p m n rz ru gens cols bfs N

@[expose] noncomputable def inM24 (f : Nat) : Bool :=
  Nat.beq (Nat.shiftRight f (24 * 5)) 0 && allN 24 (fun i => Nat.blt (pg 5 (mask 5) f i) 24) &&
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) CertificateChecks.KernelSporSch.M24Q.LR
      CertificateChecks.KernelSporSch.M24Q.TRI CertificateChecks.KernelSporSch.M24Q.BP 7 0 f

@[expose] noncomputable def xK (x g X : Nat) : Bool :=
  permB 24 5 x && permB 24 5 g && permB 24 5 X && Nat.beq (cm 24 5 g X) (cm 24 5 x g) && inM24 g

@[expose] noncomputable def elK (X : Nat) (E : List Nat) : Bool :=
  allR (fun e => permB 24 5 e && Nat.beq (cm 24 5 e X) (cm 24 5 X e) && inM24 e) E &&
    CFSG.KC.J4Q.distinctK E

@[expose] noncomputable def tailK (X : Nat) (rels : List (Nat × Nat × Nat)) (E : List Nat) : Bool :=
  allN (rcnt (CertificateChecks.KernelSporSch.M24Q.LR 0))
    (ptailBranchK 24 5 CertificateChecks.KernelSporSch.M24Q.LR
      CertificateChecks.KernelSporSch.M24Q.TR CertificateChecks.KernelSporSch.M24Q.BP X (pw 24 5 X)
      rels (lenR E) (CFSG.KC.J4Q.getN 0 E) 7)

theorem row31 : chk r31prog 31 27 10 r31z r31u r31gens r31cols r31bfs r31N = true := by
  quickRfl

theorem mask31 : maskChkK r31cols r31pi starMasks = true := by quickRfl

theorem ce31 : Nat.beq (ceCntK r31cols) 8 = true := by quickRfl

theorem x31 : xK r31x r31g r31X = true := by quickRfl

theorem rels31 : relsK 24 5 10 CertificateChecks.KernelSporSch.M24Q.BP r31X 7 r31rels = true := by
  quickRfl

theorem el31 : elK r31X r31E = true := by quickRfl

theorem tail31 : tailK r31X r31rels r31E = true := by quickRfl

theorem row43 : chk r43prog 43 22 14 r43z r43u r43gens r43cols r43bfs r43N = true := by
  quickRfl

theorem mask43 : maskChkK r43cols r43pi starMasks = true := by quickRfl

theorem ce43 : Nat.beq (ceCntK r43cols) 4 = true := by quickRfl

theorem x43 : xK r43x r43g r43X = true := by quickRfl

theorem rels43 : relsK 24 5 14 CertificateChecks.KernelSporSch.M24Q.BP r43X 7 r43rels = true := by
  quickRfl

theorem el43 : elK r43X r43E = true := by quickRfl

theorem tail43 : tailK r43X r43rels r43E = true := by quickRfl

end CertificateChecks.KernelJ4Row

end
