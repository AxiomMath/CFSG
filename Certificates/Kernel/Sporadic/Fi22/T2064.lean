module

public import Certificates.Kernel.Sporadic.Fi22.P2064
public import Certificates.Kernel.Sporadic.Fi22.E2065
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Data.Kernel.Spor.MulTree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CtiX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulTree CFSG.Sporadic.FischerOddCore

@[expose] noncomputable def bp (t : Nat) : Nat := ([0, 1, 2, 3, 6, 4] : List Nat).getD t 0

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 3510 12 (mask 12) (3510 * 12) p

@[expose] noncomputable def bOr (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 3510 12 (mask 12) p q
@[expose] noncomputable def pw (p k : Nat) : Nat := ppow 3510 12 (mask 12) (pidn 3510 12) p k

@[expose] noncomputable def Q (j : Nat) : Nat := Fi22CtiQ.T j
@[expose] noncomputable def gL (k : Nat) : Nat := Fi22CentT.L (Nat.add 19 k)
@[expose] noncomputable def gI (k : Nat) : Nat := Fi22E2065.CI (Nat.add 19 k)

@[expose] noncomputable def pq (j x : Nat) : Nat := pg 12 (mask 12) (Q j) x
@[expose] noncomputable def zf (x : Nat) : Nat := pg 12 (mask 12) (Q 20) x

@[expose] noncomputable def PA (i : Nat) : Nat := pg 12 (mask 12) Fi22CtiT.Par.F i
@[expose] noncomputable def LA (i : Nat) : Nat := pg 4 (mask 4) Fi22CtiT.Lab.F i
@[expose] noncomputable def NX (j : Nat) : Nat := pg 12 (mask 12) Fi22CtiT.Nxt.F j
@[expose] noncomputable def CD (i : Nat) : Nat := pg 12 (mask 12) Fi22CtiT.Cid.F i
@[expose] noncomputable def RP (c : Nat) : Nat := pg 12 (mask 12) Fi22CtiT.Reps.F c
@[expose] noncomputable def ZI (i : Nat) : Nat := pg 12 (mask 12) Fi22CtiT.Zi.F i
@[expose] noncomputable def PI (k c : Nat) : Nat :=
  pg 10 (mask 10) Fi22CtiT.S5.F (Nat.add (Nat.mul 512 k) c)

@[expose] noncomputable def E (i z : Nat) : Nat := ev 12 Q PA LA 1024 i z

@[expose] noncomputable def kd (i t : Nat) : Nat := pg 12 (mask 12) (Fi22CtiK.T i) t

@[expose] noncomputable def kv (i : Nat) : Nat :=
  Nat.add (kd i 0) (Nat.mul 3510 (Nat.add (kd i 1) (Nat.mul 3510 (Nat.add (kd i 2)
    (Nat.mul 3510 (Nat.add (kd i 3) (Nat.mul 3510 (Nat.add (kd i 4) (Nat.mul 3510
      (Nat.add (kd i 5) (Nat.mul 3510 0)))))))))))

@[expose] noncomputable def SG (m : Nat) : Nat := Fi22CtiS.T m

@[expose] noncomputable def MM (k j : Nat) : Nat := pg 12 (mask 12) (Fi22CtiM.T k) j

@[expose] noncomputable def qRow (j : Nat) : Bool :=
  bAnd(cn (Q j), bAnd(cn (Q (Nat.add 10 j)),
    permOK 3510 12 (mask 12) (3510 * 12) (Q j) (Q (Nat.add 10 j))))

theorem qRows : allN 10 qRow = true := by quickRfl

theorem qEq0 : Nat.beq (Q 0) (gL 0) = true := by quickRfl
theorem qEq1 : Nat.beq (Q 1) (pw (pc (gL 1) (gL 7)) 9) = true := by quickRfl
theorem qEq2 : Nat.beq (Q 2) (pw (pc (gL 2) (gL 6)) 6) = true := by quickRfl
theorem qEq3 : Nat.beq (Q 3) (pw (pc (gL 3) (gL 8)) 4) = true := by quickRfl
theorem qEq4 : Nat.beq (Q 4) (pw (pc (gL 4) (gL 7)) 4) = true := by quickRfl
theorem qEq5 : Nat.beq (Q 5) (pw (pc (gL 5) (gL 6)) 2) = true := by quickRfl
theorem qEq6 : Nat.beq (Q 6) (pw (pc (gL 6) (gL 8)) 4) = true := by quickRfl
theorem qEq7 : Nat.beq (Q 7) (pc (gL 1) (pc (Q 2) (gI 1))) = true := by quickRfl
theorem qEq8 : Nat.beq (Q 8) (pc (gL 3) (pc (Q 2) (gI 3))) = true := by quickRfl
theorem qEq9 : Nat.beq (Q 9) (pc (gL 4) (pc (Q 2) (gI 4))) = true := by quickRfl
theorem zEq : bAnd(cn (Q 20), Nat.beq (Q 20) (pc (Q 6) (pc (Q 2) (pc (Q 16) (Q 12))))) =
    true := by quickRfl
theorem idOK : bAnd(idK 3510 12 (mask 12), cn (pidn 3510 12)) = true := by quickRfl

@[expose] noncomputable def gRow (k : Nat) : Bool := bAnd(cn (gL k), cn (gI k))

theorem gRows : allN 9 gRow = true := by quickRfl

theorem zFacts : bAnd(Bool.not (allN 6 (fun t => Nat.beq (zf (bp t)) (bp t))),
    bAnd(allN 6 (fun t => Nat.beq (zf (zf (bp t))) (bp t)),
      allN 9 (fun k => allN 6 (fun t => Nat.beq (pg 12 (mask 12) (gL k) (zf (bp t)))
        (zf (pg 12 (mask 12) (gL k) (bp t))))))) = true := by quickRfl

@[expose] noncomputable def inCo (f : Nat → Nat) (r : Nat) : Bool :=
  bOr (allN 6 (fun t => Nat.beq (f t) (kd r t))) (allN 6 (fun t => Nat.beq (f t) (E r (zf (bp t)))))

@[expose] noncomputable def cj (k r t : Nat) : Nat :=
  pg 12 (mask 12) (gL k) (E r (pg 12 (mask 12) (gI k) (bp t)))

@[expose] noncomputable def rowOK (i : Nat) : Bool :=
  bAnd(bIf(Nat.beq i 0, true, bAnd(Nat.blt (PA i) i, Nat.blt (LA i) 10)),
  bAnd(allN 6 (fun t => Nat.beq (kd i t) (E i (bp t))),
  bAnd(allN 10 (fun k => strictB (NX (Nat.add (Nat.mul i 10) k)) (fun j =>
      bAnd(Nat.blt j 1024, allN 6 (fun t => Nat.beq (kd j t) (pq k (kd i t)))))),
  bAnd(strictB (CD i) (fun c => bAnd(Nat.blt c 512, strictB (ZI i) (fun y =>
      bAnd(Nat.blt y 1024, bAnd(allN 6 (fun t => Nat.beq (kd y t) (E i (zf (bp t)))),
      bAnd(Nat.beq (CD y) c, inCo (fun t => kd i t) (RP c))))))),
    bAnd(Nat.blt (SG i) 1024,
      bIf(Nat.blt (Nat.add i 1) 1024, Nat.blt (kv (SG i)) (kv (SG (Nat.add i 1))), true))))))

@[expose] noncomputable def repRow (c : Nat) : Bool :=
  strictB (RP c) (fun r => bAnd(Nat.blt r 1024, bAnd(Nat.beq (CD r) c,
  bAnd(allN 10 (fun j => bOr (allN 6 (fun t => Nat.beq (pq j (kd r t)) (E r (pq j (bp t)))))
      (allN 6 (fun t => Nat.beq (pq j (kd r t)) (E r (zf (pq j (bp t))))))),
    allN 9 (fun k => strictB (PI k c) (fun p => bAnd(Nat.blt p 512,
      inCo (fun t => cj k r t) (RP p))))))))

@[expose] noncomputable def memRow (k : Nat) : Bool :=
  allN 10 (fun j => strictB (MM k j) (fun m => bAnd(Nat.blt m 1024, allN 6 (fun t =>
    Nat.beq (kd m t) (pg 12 (mask 12) (gL k) (pq j (pg 12 (mask 12) (gI k) (bp t))))))))

theorem memRows : allN 9 memRow = true := by quickRfl

@[expose] noncomputable def rowSl (q : Nat) : Bool :=
  allN 8 (fun d => rowOK (Nat.add (Nat.mul q 8) d))

@[expose] noncomputable def repSl (q : Nat) : Bool :=
  allN 8 (fun d => repRow (Nat.add (Nat.mul q 8) d))

end CertificateChecks.KernelSpor.Fi22CtiX

#kon_slices CertificateChecks.KernelSpor.Fi22CtiX.rowSl 0 128
#kon_join CertificateChecks.KernelSpor.Fi22CtiX.rowAll CertificateChecks.KernelSpor.Fi22CtiX.rowSl 128
#kon_slices CertificateChecks.KernelSpor.Fi22CtiX.repSl 0 64
#kon_join CertificateChecks.KernelSpor.Fi22CtiX.repAll CertificateChecks.KernelSpor.Fi22CtiX.repSl 64

end
