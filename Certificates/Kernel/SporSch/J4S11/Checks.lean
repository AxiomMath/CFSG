module

public import Certificates.Data.Kernel.SporSch.J4S11
public import Certificates.Data.Kernel.SporSch.J4SRun
public import Certificates.Data.Kernel.SporSch.J4SBig
public import Certificates.Data.Kernel.SporSch.J4SPairK
public import Certificates.Data.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.MatData
public import CFSG.Sporadic.Schreier.J4SElevenData
public meta import CFSG.Sporadic.Schreier.J4SElevenData
public meta import Certificates.Kernel.SporSch.J4S.Gen
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec
public import Certificates.Kernel.SporSch.J4S.Gen

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4E7.M7 CFSG.Sporadic.J4Schreier.max7Regs
#kss_pairs CertificateChecks.KernelSporSch.J4E7.M4 CFSG.Sporadic.J4Schreier.regsN

namespace CertificateChecks.KernelSporSch.J4E7

open CFSG.Sporadic.J4Schreier in
meta def dvN : Array Pair :=
  #[S5n, X0n, Y0n, QXn, QYn, QZn, U8n, W2n, C23n, qWord 7 3 2, qWord 3 3 9, qWord 8 6 3,
    qWord 10 5 8, powP QZn 2]

end CertificateChecks.KernelSporSch.J4E7

#kss_pairs CertificateChecks.KernelSporSch.J4E7.DV CertificateChecks.KernelSporSch.J4E7.dvN
#kss_rows CertificateChecks.KernelSporSch.J4E7.FPx CFSG.Sporadic.J4Schreier.fixP_qx
#kss_rows CertificateChecks.KernelSporSch.J4E7.FIx CFSG.Sporadic.J4Schreier.fixPinv_qx
#kss_rows CertificateChecks.KernelSporSch.J4E7.FRx CFSG.Sporadic.J4Schreier.fixR_qx
#kss_rows CertificateChecks.KernelSporSch.J4E7.FPy CFSG.Sporadic.J4Schreier.fixP_qy
#kss_rows CertificateChecks.KernelSporSch.J4E7.FIy CFSG.Sporadic.J4Schreier.fixPinv_qy
#kss_rows CertificateChecks.KernelSporSch.J4E7.FRy CFSG.Sporadic.J4Schreier.fixR_qy
#kss_rows CertificateChecks.KernelSporSch.J4E7.FPz CFSG.Sporadic.J4Schreier.fixP_qz
#kss_rows CertificateChecks.KernelSporSch.J4E7.FIz CFSG.Sporadic.J4Schreier.fixPinv_qz
#kss_rows CertificateChecks.KernelSporSch.J4E7.FRz CFSG.Sporadic.J4Schreier.fixR_qz
#kss_rows CertificateChecks.KernelSporSch.J4E7.FPc CFSG.Sporadic.J4Schreier.fixP_c23
#kss_rows CertificateChecks.KernelSporSch.J4E7.FIc CFSG.Sporadic.J4Schreier.fixPinv_c23
#kss_rows CertificateChecks.KernelSporSch.J4E7.FRc CFSG.Sporadic.J4Schreier.fixR_c23

namespace CertificateChecks.KernelSporSch.J4E7

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E
open CFSG.Sporadic.J4Schreier

@[expose] def CODES : List (List Nat) :=
  [[0, 1, 2, 3], [0, 3, 2, 4], [0, 3, 4, 5], [0, 3, 5, 6], [0, 6, 4, 5], [2, 4, 4, 3],
    [2, 8, 5, 4], [1, 4, 5], [0, 5, 3, 6], [0, 6, 4, 3], [0, 1, 3, 4], [0, 4, 3, 5], [2, 3, 5, 6],
    [0, 4, 4, 5], [0, 6, 5, 3], [2, 6, 4, 5], [0, 5, 3, 4], [2, 20, 4, 3], [0, 3, 2, 5],
    [0, 2, 3, 6], [1, 6, 3], [0, 3, 5, 6], [2, 3, 6, 2], [0, 4, 2, 3], [0, 4, 3, 5], [2, 7, 5, 3],
    [1, 4, 5], [0, 5, 2, 6], [0, 2, 6, 5], [2, 8, 4, 2], [0, 2, 5, 6], [1, 6, 5], [0, 1, 4, 2],
    [0, 5, 3, 4], [0, 4, 6, 1]]

@[expose] noncomputable def INIT7 : List Nat :=
  [one, A, B, one, one, one, one, one, one, one, A, Bi, one, one, one, one, one, one]

@[expose] noncomputable def E9 : List Nat :=
  M7.take 7 ++ [one, one] ++ M7.drop 7 ++ [one, one]

@[expose] noncomputable def mP (p q : Nat × Nat) : Nat × Nat := (mulJ c rm p.1 q.1, mulJ c rm q.2 p.2)
@[expose] noncomputable def iP (p : Nat × Nat) : Nat × Nat := (p.2, p.1)
@[expose] noncomputable def pP (p : Nat × Nat) (e : Nat) : Nat × Nat :=
  (powJ c rm one p.1 e, powJ c rm one p.2 e)
@[expose] noncomputable def cP (p q : Nat × Nat) : Nat × Nat := mP (mP (mP p q) (iP p)) (iP q)
@[expose] noncomputable def eqP (p q : Nat × Nat) : Bool := andB (Nat.beq p.1 q.1) (Nat.beq p.2 q.2)

@[expose] noncomputable def H1 : Nat × Nat := (getN one M7 1, getN one M7 8)
@[expose] noncomputable def H2 : Nat × Nat := (getN one M7 2, getN one M7 9)
@[expose] noncomputable def XN : Nat × Nat := (getN one M4 1, getN one M4 10)
@[expose] noncomputable def YN : Nat × Nat := (getN one M4 2, getN one M4 11)
@[expose] noncomputable def V (k : Nat) : Nat × Nat := (getN one DV k, getN one DV (Nat.add 14 k))

theorem parse : (parseK max7Text.toList == some CODES) = true := by quickRfl

theorem lts : (CODES.map decodeK).all (CFSG.Sporadic.GLQ.Instr.lt 7) = true := by decide +kernel

theorem run : (runPK c rm one INIT7 (CODES.map decodeK) == E9) = true := by quickRfl

theorem d0 : eqP (V 0) (pP H2 8) = true := by quickRfl
theorem d1 : eqP (V 1) (mP (mP (mP (V 0) (iP H1)) (iP (V 0))) H1) = true := by quickRfl
theorem d2 : eqP (V 2) (cP (V 0) (mP H1 H2)) = true := by quickRfl
theorem d3 : eqP (V 3) (mP (V 1) (pP (V 2) 7)) = true := by quickRfl
theorem d4 : eqP (V 4) (pP (V 2) 3) = true := by quickRfl
theorem d5 : eqP (V 5) (cP (V 3) (V 4)) = true := by quickRfl
theorem d6 : eqP (V 6) (pP H2 5) = true := by quickRfl
theorem d7 : eqP (V 7) (mP (mP (mP (pP (V 3) 3) (pP (V 4) 9)) (V 5))
    (wFK c rm one H1.1 H1.2 H2.1 H2.2 [1, 2, 1, 2, 2, 2, 2] one,
      wSK c rm one H1.1 H1.2 H2.1 H2.2 [1, 2, 1, 2, 2, 2, 2] one)) = true := by quickRfl
theorem d8 : eqP (V 8) (powBJ c rm one 25 (wFK c rm one XN.1 XN.2 YN.1 YN.2 [1, 2] one) 10644480,
    powBJ c rm one 25 (wSK c rm one XN.1 XN.2 YN.1 YN.2 [1, 2] one) 10644480) = true := by quickRfl
theorem d9 : eqP (V 9) (mP (mP (pP (V 3) 7) (pP (V 4) 3)) (pP (V 5) 2)) = true := by quickRfl
theorem d10 : eqP (V 10) (mP (mP (pP (V 3) 3) (pP (V 4) 3)) (pP (V 5) 9)) = true := by quickRfl
theorem d11 : eqP (V 11) (mP (mP (pP (V 3) 8) (pP (V 4) 6)) (pP (V 5) 3)) = true := by quickRfl
theorem d12 : eqP (V 12) (mP (mP (pP (V 3) 10) (pP (V 4) 5)) (pP (V 5) 8)) = true := by quickRfl
theorem d13 : eqP (V 13) (pP (V 5) 2) = true := by quickRfl

theorem px : packNK fixP_qx.toList FPx = true := by quickRfl
theorem ix : packNK fixPinv_qx.toList FIx = true := by quickRfl
theorem rx : packNK fixR_qx.toList FRx = true := by quickRfl
theorem py : packNK fixP_qy.toList FPy = true := by quickRfl
theorem iy : packNK fixPinv_qy.toList FIy = true := by quickRfl
theorem ry : packNK fixR_qy.toList FRy = true := by quickRfl
theorem pz : packNK fixP_qz.toList FPz = true := by quickRfl
theorem iz : packNK fixPinv_qz.toList FIz = true := by quickRfl
theorem rz : packNK fixR_qz.toList FRz = true := by quickRfl
theorem pc : packNK fixP_c23.toList FPc = true := by quickRfl
theorem ic : packNK fixPinv_c23.toList FIc = true := by quickRfl
theorem rc : packNK fixR_c23.toList FRc = true := by quickRfl

@[expose] noncomputable def QX : Nat := getN one DV 3
@[expose] noncomputable def QY : Nat := getN one DV 4
@[expose] noncomputable def QZ : Nat := getN one DV 5

theorem basic : andB (Nat.beq (mulJ c rm QZ QX) (mulJ c rm QX QZ))
    (andB (Nat.beq (mulJ c rm QZ QY) (mulJ c rm QY QZ))
      (notB (Nat.beq (vecJ rm (nat_lit 1) QZ) (nat_lit 1)))) = true := by quickRfl

theorem exp : expK c rm one QX QY QZ = true := by quickRfl

theorem cen : centerK c rm one QX QY = true := by quickRfl

theorem nf : distK rm 11 [QX, QY, QZ] 1331 = true := by quickRfl

theorem conj : andB (Nat.beq (mulJ c rm H1.1 QX) (mulJ c rm (V 9).1 H1.1))
    (andB (Nat.beq (mulJ c rm H1.1 QY) (mulJ c rm (V 10).1 H1.1))
    (andB (Nat.beq (mulJ c rm H1.1 QZ) (mulJ c rm QZ H1.1))
    (andB (Nat.beq (mulJ c rm H2.1 QX) (mulJ c rm (V 11).1 H2.1))
    (andB (Nat.beq (mulJ c rm H2.1 QY) (mulJ c rm (V 12).1 H2.1))
      (Nat.beq (mulJ c rm H2.1 QZ) (mulJ c rm (V 13).1 H2.1)))))) = true := by quickRfl

theorem fixX : fixK c rm one QX FPx FIx FRx 12 = true := by quickRfl
theorem fixY : fixK c rm one QY FPy FIy FRy 12 = true := by quickRfl
theorem fixZ : fixK c rm one QZ FPz FIz FRz 2 = true := by quickRfl
theorem fixC : fixK c rm one (V 8).1 FPc FIc FRc 2 = true := by quickRfl

theorem six : andB (Nat.beq (powJ c rm one (V 6).1 8) one)
    (andB (Nat.beq (mulJ c rm (V 7).1 (V 7).1) one)
    (andB (Nat.beq (mulJ c rm (V 7).1 (V 6).1) (mulJ c rm (powJ c rm one (V 6).1 3) (V 7).1))
      (distK rm 8 [(V 6).1, (V 7).1] 16))) = true := by quickRfl

end CertificateChecks.KernelSporSch.J4E7

end
