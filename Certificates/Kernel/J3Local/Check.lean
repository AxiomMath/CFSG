module

public import Certificates.Data.Kernel.J3LocalK
public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Kernel.Sporadic.J3K.Defs
public import CFSG.RankThree.Asc83Table.J3Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Certificates.Kernel.J3Local.Rec

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelJ3L

open CFSG.KC.J3Loc CFSG.KC.OpsK CFSG.KC.M1F2

@[expose] noncomputable def lanesSrc : Nat := lanesP KernelSpor.J3K.PJ 20520
@[expose] noncomputable def onesSrc : Nat := onesL 20520
@[expose] noncomputable def regsSrc : Nat :=
  CFSG.KC.J3Rec.packL (CFSG.KC.J3Rec.runL (opsF2K 80) CFSG.RankThree.Asc83Table.J3.j3Cert.prog
    (CFSG.KC.OpsMN.initN (opsF2K 80) JA.M JB.M CFSG.RankThree.Asc83Table.J3.j3Cert.nregs))

end CertificateChecks.KernelJ3L

#j3_kw_nat CertificateChecks.KernelJ3L.Lv CertificateChecks.KernelJ3L.lanesSrc
#j3_kw_nat CertificateChecks.KernelJ3L.Ev CertificateChecks.KernelJ3L.onesSrc
#j3_kw_list CertificateChecks.KernelJ3L.Rv CertificateChecks.KernelJ3L.regsSrc 8192 419

namespace CertificateChecks.KernelJ3L

open CFSG.KC.J3Loc CFSG.KC.OpsK CFSG.KC.M1F2 CFSG.KC.OpsMN CFSG.KC.J3Rec
open CFSG.RankThree.Asc83Table.Native CFSG.RankThree.Asc83Table.J3


theorem jL : Nat.beq (lanesP KernelSpor.J3K.PJ 20520) Lv = true := by quickRfl

theorem jE : Nat.beq (onesL 20520) Ev = true := by quickRfl

theorem jR : eqNL (runL (opsF2K 80) CFSG.RankThree.Asc83Table.J3.j3Cert.prog
    (initN (opsF2K 80) JA.M JB.M CFSG.RankThree.Asc83Table.J3.j3Cert.nregs)) Rv = true := by
  quickRfl

theorem jC : certN (opsF2K 80) Rv CFSG.RankThree.Asc83Table.J3.j3Cert.mcert = true := by quickRfl

theorem jX1 : rangeK j3Cert = true := by
  quickRfl

theorem jX2 : (List.range 26).all (fun k => Nat.beq (Nat.lor (movedL (tF (evalWN (opsF2K 80) Rv
    (basisW j3Cert.rb (k + 1)))) Lv Ev) (xsMask j3Cert.xs)) Ev) = true := by
  quickRfl

theorem jX3 : Nat.beq (colK (getN Rv j3Cert.rb.1) (KernelSpor.J3K.PJ 0)) (KernelSpor.J3K.PJ 0) =
    true := by
  quickRfl

theorem jX4 : (List.range 24).all (fun k => (opsF2K 80).vne (colK (evalWN (opsF2K 80) Rv (basisW
    j3Cert.rb (k + 3))) (KernelSpor.J3K.PJ 0)) (KernelSpor.J3K.PJ 0)) = true := by
  quickRfl

theorem jX5 : (List.range 26).all (fun k => !(opsF2K 80).eq (evalWN (opsF2K 80) Rv (basisW
    j3Cert.rb (k + 1))) (opsF2K 80).one) = true := by
  quickRfl

theorem jX6 : j3Cert.ss.all (fun s => Nat.beq (colK (getN Rv s.1) (KernelSpor.J3K.PJ 0))
    (KernelSpor.J3K.PJ 0)) = true := by
  quickRfl

theorem jX7 : (j3Cert.cs.map (getN Rv)).zipIdx.all (fun p => ((j3Cert.cs.map (getN Rv)).zip
    ((j3Cert.cs.map (getN Rv)).map fun X => powN (opsF2K 80) 3 X 2)).zipIdx.all fun q => Nat.beq
    p.2 q.2 || (!(opsF2K 80).eq p.1 q.1.1 && !(opsF2K 80).eq p.1 q.1.2)) = true := by
  quickRfl

theorem jX8 : (List.range 27).all (fun k => (List.range 8).all fun m =>
    !(opsF2K 80).eq (powN (opsF2K 80) 4 (evalWN (opsF2K 80) Rv
      (basisW j3Cert.rb k ++ hW j3Cert.rh (m + 1))) 3) (opsF2K 80).one) = true := by
  quickRfl

theorem jX9 : Nat.beq j3Cert.ss.length j3Cert.cs.length = true := by
  quickRfl

theorem jX : extraK CFSG.RankThree.Asc83Table.J3.j3Cert (KernelSpor.J3K.PJ 0) Lv Ev Rv = true :=
  extraK_of jX1 jX2 jX3 jX4 jX5 jX6 jX7 jX8 jX9

theorem full_K : fullK JA.M JB.M KernelSpor.J3K.PJ 20520 CFSG.RankThree.Asc83Table.J3.j3Cert =
    true :=
  fullK_of (Nat.eq_of_beq_eq_true jL) (Nat.eq_of_beq_eq_true jE) (eq_of_eqNL jR) jC jX

theorem range_neg : (!rangeK { CFSG.RankThree.Asc83Table.J3.j3Cert with nregs := 3 }) = true := by
  quickRfl

theorem moved_neg : (!Nat.beq (movedL (tF (idF 80))
    (lanesP KernelSpor.J3K.PJ 4) (onesL 4)) (onesL 4)) = true := by
  quickRfl

end CertificateChecks.KernelJ3L

end
