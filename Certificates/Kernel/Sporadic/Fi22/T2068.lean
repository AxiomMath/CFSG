
module

public import Certificates.Kernel.Sporadic.Fi22.P2068
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import Certificates.Kernel.Sporadic.ON.Gen
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22LabX

meta def out6M : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong3510 6

end CertificateChecks.KernelSpor.Fi22LabX

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22LabX.O6
  CertificateChecks.KernelSpor.Fi22LabX.out6M 12

namespace CertificateChecks.KernelSpor.Fi22LabX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Text CFSG.Sporadic.FischerOddCore

@[expose] noncomputable def memP (q : Nat) : Bool := bAnd(Fi22X.cn q, Fi22X.siftP q)

@[expose] noncomputable def Lx (L : Nat) : Nat := Fi22ExtT.L L
@[expose] noncomputable def LI (L : Nat) : Nat := Fi22E2067.EI L

@[expose] noncomputable def tr (o k y : Nat) : Nat := pg 12 (mask 12) (Fi22TC.TR (Nat.add o k)) y

@[expose] noncomputable def XI (I y : Nat) : Nat :=
  strictN (Nat.div I 2) (fun j =>
    pg 12 (mask 12) (Lx 0) (tr 0 (Nat.mod (Nat.div (Nat.div j 4) 32) 1024)
      (tr 1024 (Nat.mod (Nat.div j 4) 32) (tr 1056 (Nat.mod j 4)
        (pg 12 (mask 12) (LI 0) (nIf(Nat.beq (Nat.mod I 2) 1, pg 12 (mask 12) (Lx 1) y, y)))))))

@[expose] noncomputable def bs (t : Nat) : Nat := ([0, 1, 2, 3, 4, 6] : List Nat).getD t 0

@[expose] noncomputable def Db (t : Nat) : Nat := pg 12 (mask 12) Fi22X.DP (bs t)

@[expose] noncomputable def isInvK (I : Nat) : Bool :=
  bAnd(Bool.not (allN 6 (fun t => Nat.beq (XI I (Db t)) (Db t))),
    allN 6 (fun t => Nat.beq (XI I (XI I (Db t))) (Db t)))

@[expose] noncomputable def PP (I : Nat) : Nat :=
  pg 16 (mask 16) (Fi22LabP.T (Nat.div I 8192)) (Nat.mod I 8192)
@[expose] noncomputable def RF (k f : Nat) : Nat :=
  pg 20 (mask 20) (Fi22LabT.Rec.L (Nat.div k 128)) (Nat.add (Nat.mul (Nat.mod k 128) 15) f)
@[expose] noncomputable def LB (k : Nat) : Nat := RF k 0
@[expose] noncomputable def PR (k : Nat) : Nat := RF k 1
@[expose] noncomputable def GN (k : Nat) : Nat := RF k 2
@[expose] noncomputable def DE (k : Nat) : Nat := RF k 3
@[expose] noncomputable def NB (t : Nat) : Nat := RF (Nat.div t 10) (Nat.add 4 (Nat.mod t 10))

@[expose] noncomputable def labOf (J : Nat) : Nat :=
  strictN (PP J) (fun k => nIf(Nat.blt k 6143, LB k, 79))
@[expose] noncomputable def depOf (J : Nat) : Nat :=
  strictN (PP J) (fun k => nIf(Nat.blt k 6143, DE k, 0))

@[expose] noncomputable def RT (j : Nat) : Nat := Fi22LabR.T j
@[expose] noncomputable def SV (k : Nat) : Nat := RF k 14

@[expose] noncomputable def conjB (s I J : Nat) : Bool :=
  allN 6 (fun t => Nat.beq (XI I (Db t)) (pg 12 (mask 12) (Lx (Nat.add 11 s))
    (XI J (pg 12 (mask 12) (LI (Nat.add 11 s)) (Db t)))))

@[expose] noncomputable def rowI (I : Nat) : Bool :=
  strictB (PP I) (fun k => bIf(isInvK I,
    bAnd(Nat.blt k 6143, bAnd(Nat.beq (SV k) I, strictB (LB k) (fun l => bAnd(Nat.blt l 79,
    bAnd(bIf(Nat.beq (DE k) 0, Nat.beq I (RT l),
        strictB (PR k) (fun J => strictB (GN k) (fun s => bAnd(Nat.blt J 262144,
          bAnd(Nat.blt (depOf J) (DE k), bAnd(Nat.beq (labOf J) l,
            bAnd(Nat.blt s 10, conjB s I J))))))),
      allN 10 (fun s => strictB (NB (Nat.add (Nat.mul k 10) s)) (fun J =>
        bAnd(Nat.blt J 262144, bAnd(Nat.beq (labOf J) l, conjB s J I))))))))),
    Nat.beq k 6143))

@[expose] noncomputable def invRow (k : Nat) : Bool :=
  bAnd(Nat.beq (PP (SV k)) k, bAnd(Nat.blt (SV k) 262144,
    bIf(Nat.blt (Nat.add k 1) 6143, Nat.blt (SV k) (SV (Nat.add k 1)), true)))

@[expose] noncomputable def rootRow (j : Nat) : Bool :=
  bAnd(Nat.beq (fi22ExtRootsRec[j]!) (RT j), bAnd(Nat.blt (RT j) 262144,
    bAnd(Nat.beq (labOf (RT j)) j,
      allN 3510 (fun p => Nat.beq (XI (RT j) p) (pg 12 (mask 12) (Lx (Nat.add 27 j)) p)))))

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 3510 12 (mask 12) p q

@[expose] noncomputable def gc (j : Nat) : Nat := fi22ExtGlobalClasses.getD j 0

@[expose] noncomputable def conjRow (j : Nat) : Bool :=
  bAnd(memP (Lx (Nat.add 106 j)), bAnd(Fi22X.cn (Lx (Nat.add 27 j)),
    bAnd(Fi22X.cn (Lx (Nat.add 21 (gc j))),
      Nat.beq (pc (Lx (Nat.add 106 j)) (Lx (Nat.add 27 j)))
        (pc (Lx (Nat.add 21 (gc j))) (Lx (Nat.add 106 j))))))

@[expose] noncomputable def fixK (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (nIf(Nat.beq (pg 12 (mask 12) p i) i, 1, 0))) 3510

theorem repFacts : bAnd(allN 3 (fun i => Nat.beq (Lx (Nat.add 21 i)) (O6 i)),
    bAnd(Nat.beq (Lx 24) Fi22X.GO,
    bAnd(allN 6 (fun k => bAnd(neIdK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) (Lx (Nat.add 21 k)),
      sqIdK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) (Lx (Nat.add 21 k)))),
    bAnd(Nat.beq (fixK (Lx 21)) 54, bAnd(Nat.beq (fixK (Lx 22)) 182,
    bAnd(Nat.beq (fixK (Lx 23)) 694, bAnd(Nat.beq (fixK (Lx 24)) 72,
    bAnd(Nat.beq (fixK (Lx 25)) 360, bAnd(Nat.beq (fixK (Lx 26)) 64,
    bAnd(allN 3 (fun k => memP (Lx (Nat.add 21 k))),
      allN 3 (fun k => bAnd(Fi22X.cn (Lx (Nat.add 24 k)), bAnd(bIf(Fi22X.siftP (Lx (Nat.add 24 k)), false, true),
        bAnd(Fi22X.cn (pc Fi22X.GO (Lx (Nat.add 24 k))),
          Fi22X.siftP (pc Fi22X.GO (Lx (Nat.add 24 k))))))))))))))))) = true := by quickRfl

@[expose] noncomputable def labCnt (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add acc (nIf(Nat.beq (LB k) j, 1, 0))) 6143

theorem classCounts : allN 79 (fun j => Nat.beq (labCnt j) (fi22ExtClassSizes.getD j 0)) = true := by
  quickRfl

theorem offs : bAnd(Nat.beq (roff 3510 (3510 * 12) (Fi22TC.LR 0)) 0,
    bAnd(Nat.beq (roff 3510 (3510 * 12) (Fi22TC.LR 1)) 1024,
    bAnd(Nat.beq (roff 3510 (3510 * 12) (Fi22TC.LR 2)) 1056,
    bAnd(Nat.beq (rcnt (Fi22TC.LR 0)) 1024, bAnd(Nat.beq (rcnt (Fi22TC.LR 1)) 32,
      Nat.beq (rcnt (Fi22TC.LR 2)) 4))))) = true := by quickRfl

theorem out6a : asciiK (Fi22OutT.chars.take (Nat.mul (nat_lit 39) (nat_lit 10531))) = true := by
  quickRfl

@[expose] noncomputable def outL (i : Nat) : Bool :=
  lineK 3 3510 12 (O6 i) (Fi22OutT.chars.drop (Nat.mul (Nat.add (nat_lit 36) i) (nat_lit 10531)))

theorem out6l0 : outL 0 = true := by quickRfl
theorem out6l1 : outL 1 = true := by quickRfl
theorem out6l2 : outL 2 = true := by quickRfl

@[expose] noncomputable def trSl (q : Nat) : Bool :=
  allN 20 (fun d => strictB (Nat.add (Nat.mul q 20) d) (fun k =>
    bIf(Nat.blt k 1060, Fi22X.cn (Fi22TC.TR k), true)))

@[expose] noncomputable def rowSl (q : Nat) : Bool :=
  allN 512 (fun d => rowI (Nat.add (Nat.mul q 512) d))

@[expose] noncomputable def invSl (q : Nat) : Bool :=
  allN 64 (fun d => strictB (Nat.add (Nat.mul q 64) d) (fun k => bIf(Nat.blt k 6143, invRow k, true)))

@[expose] noncomputable def rootSl (q : Nat) : Bool :=
  allN 8 (fun d => strictB (Nat.add (Nat.mul q 8) d) (fun j => bIf(Nat.blt j 79, rootRow j, true)))

@[expose] noncomputable def conjSl (q : Nat) : Bool :=
  allN 8 (fun d => strictB (Nat.add (Nat.mul q 8) d) (fun j => bIf(Nat.blt j 79, conjRow j, true)))

end CertificateChecks.KernelSpor.Fi22LabX

#kon_slices CertificateChecks.KernelSpor.Fi22LabX.trSl 0 53
#kon_join CertificateChecks.KernelSpor.Fi22LabX.trAll CertificateChecks.KernelSpor.Fi22LabX.trSl 53
#kon_slices CertificateChecks.KernelSpor.Fi22LabX.rootSl 0 10
#kon_join CertificateChecks.KernelSpor.Fi22LabX.rootAll CertificateChecks.KernelSpor.Fi22LabX.rootSl 10
#kon_slices CertificateChecks.KernelSpor.Fi22LabX.conjSl 0 10
#kon_join CertificateChecks.KernelSpor.Fi22LabX.conjAll CertificateChecks.KernelSpor.Fi22LabX.conjSl 10
#kon_slices CertificateChecks.KernelSpor.Fi22LabX.invSl 0 96
#kon_join CertificateChecks.KernelSpor.Fi22LabX.invAll CertificateChecks.KernelSpor.Fi22LabX.invSl 96
#kon_slices CertificateChecks.KernelSpor.Fi22LabX.rowSl 0 512
#kon_join CertificateChecks.KernelSpor.Fi22LabX.rowAll CertificateChecks.KernelSpor.Fi22LabX.rowSl 512

end
