module

public import Certificates.Kernel.SporSch.Tits.GenSurv
public import Certificates.Kernel.SporSch.Tits.GenAll5
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.TitsOct.Data
public import Certificates.Data.Kernel.TitsN12K
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo
public meta import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public meta import Certificates.Data.RuF45Geom
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsN12

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

meta def swp (a : Array Nat) (x y : Nat) : Bool :=
  ((a[1]! == x && a[2]! == y) || (a[1]! == y && a[2]! == x)) &&
    ((a[x]! == 1 && a[y]! == 2) || (a[x]! == 2 && a[y]! == 1))

meta def pH (a : Array Nat) : Bool :=
  a[0]! == 0 && (swp a 3 4 || swp a 5 7 || swp a 9 13 || swp a 17 25) &&
    eqA 1755 (compA 1755 a a) (idA 1755)

meta def farPts : List Nat :=
  let lay := (CFSG.RuF45.layBFS titsLinePtArr (CFSG.RuF45.mkPtL titsLinePtArr) 0).1
  (List.range 1755).filter fun p => lay[p]! == 8

meta def lH : List (Array Nat) := survivors5 1755 titsHLevels pH

meta def lF : List (Array Nat) := lH.filter fun a => farPts.any fun p => a[p]! == p

meta def pN (a : Array Nat) : Bool :=
  (a[0]! == 1 || a[0]! == 2) && a[a[0]!]! == 0 && eqA 1755 (compA 1755 a a) (idA 1755)

meta def lN : List (Array Nat) := survivors5 1755 titsNLevels pN

end CertificateChecks.KernelTitsN12

#kst_surv CertificateChecks.KernelTitsN12.SH 11 CFSG.Sporadic.Schreier.Tits.titsHLevels
  CertificateChecks.KernelTitsN12.lH
#kst_surv CertificateChecks.KernelTitsN12.SF 11 CFSG.Sporadic.Schreier.Tits.titsHLevels
  CertificateChecks.KernelTitsN12.lF
#kst_surv CertificateChecks.KernelTitsN12.SN 11 CFSG.Sporadic.Schreier.Tits.titsNLevels
  CertificateChecks.KernelTitsN12.lN

#kc_repo #kc_json_gz CertificateChecks.KernelTitsN12.D "Certificates/Kernel/TitsN12/data/n12.json.gz"
  1051 13072867592665378660 (U : List Nat) (R1 : List Nat) (E1 : List (Nat × Nat × Nat)) (R2 : List Nat)
  (E2 : List (Nat × Nat × Nat)) (R4 : List Nat) (E4 : List (Nat × Nat × Nat)) (R8 : List Nat)
  (E8 : List (Nat × Nat × Nat))

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.TitsN12K
open CertificateChecks.KernelSpor

@[expose] noncomputable def PH (t0 t1 t2 t3 t4 : Nat) : Bool := swT TitsH.BP (gptR t0 t1 t2 t3 t4)

@[expose] noncomputable def QH : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PH SH.M

@[expose] noncomputable def PN (t0 t1 t2 t3 t4 : Nat) : Bool := n2T TitsN.BP (gptR t0 t1 t2 t3 t4)

@[expose] noncomputable def QN : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PN SN.M

end CertificateChecks.KernelTitsN12

#kst_all5 CertificateChecks.KernelTitsN12.EH 1755 11 10 8 CertificateChecks.KernelSpor.TitsH.LR
  CertificateChecks.KernelSpor.TitsH.TR CertificateChecks.KernelTitsN12.QH
#kst_all5 CertificateChecks.KernelTitsN12.EN 1755 11 24 2 CertificateChecks.KernelSpor.TitsN.LR
  CertificateChecks.KernelSpor.TitsN.TR CertificateChecks.KernelTitsN12.QN

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.TitsN12K
open CertificateChecks.KernelSpor

theorem mH : Nat.beq (maskOf SH.C) SH.M = true := by quickRfl
theorem aH : ascK (tot5 TitsH.LR) SH.C 0 = true := by quickRfl
theorem zH : zipK (fun c l => Nat.beq (prodCode 1755 11 (mask 11) (1755 * 11) TitsH.LR TitsH.TR c) l)
    SH.C SH.L = true := by quickRfl
theorem mN : Nat.beq (maskOf SN.C) SN.M = true := by quickRfl
theorem aN : ascK (tot5 TitsN.LR) SN.C 0 = true := by quickRfl

theorem farH : zipK (farOK CFSG.KD.TitsOct.LAY0 SF.M) SH.C SH.L = true := by quickRfl
theorem mF : Nat.beq (maskOf SF.C) SF.M = true := by quickRfl
theorem aF : ascK (tot5 TitsH.LR) SF.C 0 = true := by quickRfl
theorem sF : Nat.beq (Nat.land SF.M SH.M) SF.M = true := by quickRfl

theorem cnt3 : Nat.beq (cntAt TitsH.LR TitsH.TR 1 3 4 SF.C) 16 = true := by quickRfl
theorem cnt5 : Nat.beq (cntAt TitsH.LR TitsH.TR 1 5 7 SF.C) 16 = true := by quickRfl
theorem cnt9 : Nat.beq (cntAt TitsH.LR TitsH.TR 1 9 13 SF.C) 16 = true := by quickRfl
theorem cnt17 : Nat.beq (cntAt TitsH.LR TitsH.TR 1 17 25 SF.C) 16 = true := by quickRfl
theorem cntN1 : Nat.beq (cntAt TitsN.LR TitsN.TR 0 1 1 SN.C) 64 = true := by quickRfl
theorem cntN2 : Nat.beq (cntAt TitsN.LR TitsN.TR 0 2 2 SN.C) 64 = true := by quickRfl

@[expose] noncomputable def U (j : Nat) : Nat :=
  prodCode 1755 11 (mask 11) (1755 * 11) TitsK.LR TitsK.TR (D.U.getD j 0)

theorem uJ0 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0
    (U 0) = true := by quickRfl
theorem uJ1 : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0
    (U 1) = true := by quickRfl
theorem uLen : Nat.beq D.U.length 2 = true := by quickRfl

@[expose] noncomputable def walkU (u0 u1 : Nat) (E : List (Nat × Nat × Nat)) (R : List Nat) :
    List Nat :=
  walkK (conjOK (fun j => Bool.rec (motive := fun _ => Nat) u1 u0 (Nat.beq j 0)) SH.C SH.L) E R

@[expose] noncomputable def cntW (a b : Nat) (W : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => Bool.rec (motive := fun _ => Nat) (nat_lit 1000) (Nat.succ ih)
      (bAnd(memL c SF.C, in2 a b (gptC TitsH.LR TitsH.TR c 1)))) W

@[expose] noncomputable def walkOK (a b : Nat) (E : List (Nat × Nat × Nat)) (R : List Nat) : Bool :=
  strictB (U 0) (fun u0 => strictB (U 1) (fun u1 => Nat.beq (cntW a b (walkU u0 u1 E R)) 16))

theorem walk3 : walkOK 3 4 D.E1 D.R1 = true := by quickRfl
theorem walk5 : walkOK 5 7 D.E2 D.R2 = true := by quickRfl
theorem walk9 : walkOK 9 13 D.E4 D.R4 = true := by quickRfl
theorem walk17 : walkOK 17 25 D.E8 D.R8 = true := by quickRfl

end CertificateChecks.KernelTitsN12

end
