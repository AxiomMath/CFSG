module

public import Certificates.Data.Kernel.J4FixCE
public import Certificates.Data.Kernel.J4Q.QT
public import Certificates.Kernel.J4Count.FixCEData
public import Certificates.Kernel.J4Q.QT2AData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.MaskData
public import Certificates.Kernel.J4Q.MatData
public import CFSG.Sporadic.Schreier.J4SData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4FixCE CFSG.KD.J4FixCE CFSG.KC.Enum CFSG.KS.SporSch.C11
open CFSG.KC.J4FixC (nth notK walkK)
open CFSG.Sporadic.J4Schreier (rootBits)

@[expose] noncomputable def UL : List Nat := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

@[expose] noncomputable def GL32 : List Nat :=
  [QA_0, QA_1, QA_2, QA_3, QA_4, QA_5, QA_6, QA_7, QA_8, QA_9, QA_10, QA_11, YA, YB, YP5, YP7,
    YP11] ++ UL ++ [mkKM_0, mkKM_1, mkKM_2, mkKM_3]

theorem a3 : Nat.beq (powJ c rm one YA (nat_lit 3)) one = true := by quickRfl

theorem b3 : Nat.beq (powJ c rm one YB (nat_lit 3)) one = true := by quickRfl

theorem cm_ok : Nat.beq (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm YA YB) YA) YA) YB) YB)
    CMD = true := by quickRfl

theorem c3 : Nat.beq (powJ c rm one CMD (nat_lit 3)) one = true := by quickRfl

theorem root_fix : Nat.beq (vecJ rm rootBits CMD) rootBits = true := by quickRfl

theorem cols_ok : allN (nat_lit 11) (fun j => Nat.beq (mulJ c rm CMD (getN one UL j))
    (mulJ c rm (etaK c rm one UL (colK PC j)) CMD)) = true := by quickRfl

theorem cnt_ok : Nat.beq (fixCntK PC) (nat_lit 32) = true := by quickRfl

theorem cg_ok : allN (nat_lit 2) (fun j =>
    Nat.beq (prodK c rm one GL32 (nth [] CGW j) one) (nth (nat_lit 0) CGM j)) = true := by quickRfl

theorem comm_ok : allN (nat_lit 2) (fun j => Nat.beq (mulJ c rm (nth (nat_lit 0) CGM j) CMD)
    (mulJ c rm CMD (nth (nat_lit 0) CGM j))) = true := by quickRfl

theorem len_ok : Nat.beq PTS.length (nat_lit 737) = true := by quickRfl

theorem pts_fix : fixAllJ rm CMD PTS = true := by quickRfl

theorem pts_nodup : nodupK PTS = true := by quickRfl

theorem root_pt : Nat.beq (nth (nat_lit 0) PTS (nat_lit 0)) rootBits = true := by quickRfl

theorem p77 : Nat.beq (walkK rm A A B Bi W77 rootBits) (nth (nat_lit 0) PTS (nat_lit 77)) = true := by
  quickRfl

theorem tree_ok : allN (nat_lit 737) (treeAt rm CGM PTS PAR) = true := by quickRfl

theorem neg_cm : notK (Nat.beq (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm (mulJ c rm YB YB) YB) YB)
    YB) YB) CMD) = true := by quickRfl

theorem neg_fix : notK (fixAllJ rm CMD [Nat.xor (nth (nat_lit 0) PTS (nat_lit 1)) (nat_lit 1)]) =
    true := by quickRfl

theorem neg_nodup : notK (nodupK (nth (nat_lit 0) PTS (nat_lit 5) :: PTS)) = true := by quickRfl

theorem neg_tree : notK (allN (nat_lit 737) (treeAt rm (CGM.reverse) PTS PAR)) = true := by
  quickRfl

theorem neg_p77 : notK (Nat.beq (walkK rm A A B Bi W77.dropLast rootBits)
    (nth (nat_lit 0) PTS (nat_lit 77))) = true := by quickRfl

theorem neg_cols : notK (Nat.beq (mulJ c rm CMD (getN one UL (nat_lit 0)))
    (mulJ c rm (etaK c rm one UL (Nat.xor (colK PC (nat_lit 0)) (nat_lit 1))) CMD)) = true := by
  quickRfl

theorem neg_cnt : notK (Nat.beq (fixCntK PC) (nat_lit 33)) = true := by quickRfl

end CertificateChecks.KernelJ4Count.FixCE

end
