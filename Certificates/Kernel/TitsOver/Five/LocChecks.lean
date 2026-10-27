module

public import Certificates.Kernel.TitsOver.Five.LEnum
public import Certificates.Kernel.TitsOver.Five.LData
public import Certificates.Kernel.TitsOver.Five.LocEnum
public import Certificates.Kernel.TitsOver.Five.LocData
public import Certificates.Data.Kernel.MaxD2.Check
public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.StandardType.TitsFive

theorem c_rg : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) LE.G LGI 4
    ((Certificates.MaxD2Perm.rWs (lLocalData ()))[j]!) (CRE.G j),
    canonK 1755 11 (mask 11) (1755 * 11) (CRE.G j))) = true := by quickRfl
theorem c_rh : penumHdK (pidn 1755 11) CRE.cnt 25 CRE.T CRE.PL = true := by quickRfl
theorem c_rsl : penumSlK 1755 11 (mask 11) (1755 * 11) false CRE.G CRE.GI CRE.k CRE.cnt CRE.T CRE.PL
    CRE.POS CRE.SRT CRE.SRI 0 25 = true := by quickRfl
theorem c_nh : penumHdK (pidn 1755 11) CNE.cnt 300 CNE.T CNE.PL = true := by quickRfl
theorem c_ng : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) LE.G LGI 4
    ((lLocalData ()).nW[j]!) (CNE.G j), canonK 1755 11 (mask 11) (1755 * 11) (CNE.G j))) = true := by
  quickRfl
theorem c_ngi : allN 2 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (CNE.G j) (CNGI j)) = true := by
  quickRfl
theorem c_norm : allN 2 (fun j => allN 2 (fun i =>
    bAnd(conjInK 1755 11 CRE.cnt CRE.T (CNE.G j) (CNGI j) (CRE.G i)
      (r32 CNH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 1755 11 CRE.cnt CRE.T (CNGI j) (CNE.G j) (CRE.G i)
      (r32 CNH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem c_mv : notInK CRE.cnt CRE.T (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (LE.G 2)
    (CRE.G 0)) (LGI 2)) = true := by quickRfl
theorem c_tw : wordEqK 1755 11 (mask 11) (pidn 1755 11) LE.G LGI 4 (lLocalData ()).tW (CTT 0) =
    true := by quickRfl
theorem c_tp : permOK 1755 11 (mask 11) (1755 * 11) (CTT 0) (CTT 1) = true := by quickRfl
theorem c_th1 : Nat.blt (r32 CMISC 0) CNE.cnt = true := by quickRfl
theorem c_th2 : Nat.beq (CNE.T (r32 CMISC 0)) (CTT 0) = true := by quickRfl
theorem c_tk : torusK 1755 11 5 CRE.cnt 3 2 6 CRE.T (CTT 0) (CTT 1) = true := by quickRfl
theorem c_cent : allN CNE.cnt (fun k => centK 1755 11 CRE.cnt CNE.T CRE.T (CRE.G 0) (CRE.G 1)
    (r32 CCH k) k) = true := by quickRfl
theorem c_r0 : Nat.beq (CREP 0) (pidn 1755 11) = true := by quickRfl
theorem c_rw : wordEqK 1755 11 (mask 11) (pidn 1755 11) LE.G LGI 4 ((lLocalData ()).repW[0]!)
    (CREP 1) = true := by quickRfl
theorem c_ri : allN 2 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (CREP i) (CREPI i)) = true := by
  quickRfl
theorem c_pts1 : Nat.beq ((lLocalData ()).fpPts[0]!) (r32 CPT 0) = true := by quickRfl
theorem c_pts2 : Nat.blt (r32 CPT 0) 1755 = true := by quickRfl
theorem c_srt : allN CNE.cnt (sortK 11 1 11 CNE.cnt (r32 CPT) CNE.T CFS CKS) = true := by quickRfl
theorem c_test : repK 1755 11 1 11 CNE.cnt (r32 CPT) CNE.T CFS CKS CREP CREPI CRB CH 1 = true := by
  quickRfl
theorem c_cnt : Nat.beq (posCnt CNE.cnt CH 1) (r32 CCN 1) = true := by quickRfl
theorem c_sum : Nat.beq ((List.range 2).foldl (fun s i => s + 300 * 300 /
    (if i = 0 then CNE.cnt else r32 CCN i)) 0) 7800 = true := by quickRfl
theorem c_lab : labK 1755 11 CNE.k CNE.G (r32 CL) = true := by quickRfl
theorem c_mk : allN 2 (fun i => Nat.beq (rg 2048 (mask 2048) CMK 0 i)
    (mkeyK 1755 11 28 11 (r32 CMISC 1) (r32 CL) (CREP i))) = true := by quickRfl
theorem c_mkd : (Nat.beq (rg 2048 (mask 2048) CMK 0 0) (rg 2048 (mask 2048) CMK 0 1)).not = true := by
  quickRfl
theorem c_gen1 : Nat.beq ((lLocalData ()).genW[0]!).length 4 = true := by quickRfl
theorem c_gen2 : allN 4 (fun j => wordEqK 1755 11 (mask 11) (pidn 1755 11)
    (fun l => nIf(Nat.blt l CNE.k, CNE.G l, CREP 1))
    (fun l => nIf(Nat.blt l CNE.k, CNGI l, CREPI 1)) 3
    (((lLocalData ()).genW[0]!)[j]!) (LE.G j)) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Five

end
