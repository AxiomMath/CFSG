
module

public import Certificates.Data.Kernel.J4Five
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.X0OrbData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Data
public import CFSG.Sporadic.J4.QT2LocX0NNative
public import CFSG.Sporadic.J4.QT2LocX0KNative
public import Certificates.Kernel.SporSch.J4S.NoCK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Five

open CFSG.KC.J4Five CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4Count
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CFSG.Sporadic.J4.QT2
open CertificateChecks.KernelSporSch.J4NoCK

@[expose] noncomputable def UL : List Nat := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

@[expose] noncomputable def G5L : List Nat := [L0, L1, L2, A, B]
@[expose] noncomputable def G5iL : List Nat := [L0i, L1i, L2i, Ai, Bi]

@[expose] noncomputable def nVec (v : Nat) : Nat :=
  vwK rm one G5L G5iL nWordV (vecEtaK rm UL nMask (vwK rm one G5L G5iL nWordU v))

theorem gold_inv : invOK GB GP = true := by quickRfl

theorem gold_gen0 : genOK GB GP (getN 0 starPerm0) = true := by quickRfl

theorem gold_gen1 : genOK GB GP (getN 0 starPerm1) = true := by quickRfl

theorem gold_gen2 : genOK GB GP (getN 0 starPerm2) = true := by quickRfl

theorem gold_id : genOK GB GP (fun i => i) = true := by quickRfl

theorem gold_sq : sqOK starPerm0 starPerm1 starPerm2 YT XI = true := by quickRfl

theorem gold_pc : Nat.beq (pcN (Nat.lor (maskL FL) (maskL TL)) 24) 8 = true := by quickRfl

theorem gold_dist : distB (FL ++ TL) = true := by quickRfl

theorem gold_fix : fixOK XI FL = true := by quickRfl

theorem gold_oct0 : inC GB GP (Nat.lor (maskL FL) (maskL TL)) = true := by quickRfl

theorem gold_oct : octOK GB XI (maskL FL) (maskL TL) = true := by quickRfl

theorem gold_crd : crdOK XI CRD (FL ++ TL) = true := by quickRfl

theorem gold_cand : Nat.beq (candN GB GP XI CRD FL TL) 12 = true := by quickRfl

theorem pts_dist : distB XPTS = true := by quickRfl

theorem pts_eqv : eqvOK rm one XPTS XG PHI 14 16 = true := by quickRfl

theorem phi_lt : allN 14 (fun i => Nat.blt (getN 0 PHI i) 14) = true := by quickRfl

@[expose] def QAN : Nat := 0x449abd729301143b6704b3bae52b

theorem qan_eq : Nat.beq (getN 0 XPTS 1) QAN = true := by quickRfl

@[expose] noncomputable def cntQA : Nat :=
  cntK 2048 (fun a => Nat.beq (Nat.mod (etaK QAN a) (Nat.pow 2 112)) QAN)

theorem fix_qA : Nat.beq cntQA 128 = true := by quickRfl

theorem pts_root : Nat.beq (getN 0 XPTS 0) (v2N CFSG.Sporadic.J4.Native.rootV) = true := by quickRfl

theorem n_fix_root : Nat.beq (nVec (getN 0 XPTS 0)) (getN 0 XPTS 0) = true := by quickRfl

theorem n_fix_qA : Nat.beq (nVec (getN 0 XPTS 1)) (getN 0 XPTS 1) = true := by quickRfl

theorem n_fix_q1 : Nat.beq (nVec (v2N x0Q1)) (v2N x0Q1) = true := by quickRfl

theorem neg_cand : notB (Nat.beq (candN GB GP XI CRD FL TL) 11) = true := by quickRfl

theorem neg_oct : notB (octOK GB XI (maskL FL) (maskL [0, 3, 15, 19])) = true := by quickRfl

theorem neg_gen : notB (genOK GB GP (getN 0 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23])) = true := by quickRfl

theorem neg_fix : notB (fixOK XI [4, 10, 14]) = true := by quickRfl

theorem neg_eqv : notB (eqvOK rm one XPTS XG [0, 1, 4, 5, 2, 3, 7, 6, 11, 10, 9, 8, 13, 12] 14 16) =
    true := by quickRfl

theorem neg_fix_qA : notB (Nat.beq cntQA 127) = true := by quickRfl

theorem neg_n_fix : notB (Nat.beq (nVec (getN 0 XPTS 2)) (getN 0 XPTS 2)) = true := by quickRfl

end CertificateChecks.KernelJ4Count.Five

end
