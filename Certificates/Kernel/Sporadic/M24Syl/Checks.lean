module

public import Certificates.Data.Kernel.Spor.MSylowCent
public import Certificates.Data.Kernel.Spor.MSylowFast
public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Derivs
public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Inputs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutM24Inputs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutM24Derivs
public meta import CFSG.Sporadic.Mathieu.M24
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M24Syl

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m24gA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m24gB).toArray

meta def tZM : Array Nat := CFSG.Sporadic.Schreier.m24SylowZ.toArray

meta def tAiM : Array Nat := invA tAM

meta def tBiM : Array Nat := invA tBM

meta def tZiM : Array Nat := invA tZM

meta def oneM : Array Nat := idA 24

meta def ptM : Array Nat :=
  (CFSG.Sporadic.Schreier.m24SylowExprs.map fun e =>
    CFSG.KS.RawGen.pack 5 (evalW 24 (strongOf 24 #[tAM, tBM] CFSG.Sporadic.Schreier.m24Derivs) e)).toArray

end CertificateChecks.KernelSpor.M24Syl

#ks_perm CertificateChecks.KernelSpor.M24Syl.I 5 CertificateChecks.KernelSpor.M24Syl.oneM
#ks_perm CertificateChecks.KernelSpor.M24Syl.A 5 CertificateChecks.KernelSpor.M24Syl.tAM
#ks_perm CertificateChecks.KernelSpor.M24Syl.Ai 5 CertificateChecks.KernelSpor.M24Syl.tAiM
#ks_perm CertificateChecks.KernelSpor.M24Syl.B 5 CertificateChecks.KernelSpor.M24Syl.tBM
#ks_perm CertificateChecks.KernelSpor.M24Syl.Bi 5 CertificateChecks.KernelSpor.M24Syl.tBiM
#ks_perm CertificateChecks.KernelSpor.M24Syl.Z 5 CertificateChecks.KernelSpor.M24Syl.tZM
#ks_perm CertificateChecks.KernelSpor.M24Syl.Zi 5 CertificateChecks.KernelSpor.M24Syl.tZiM
#kss_list CertificateChecks.KernelSpor.M24Syl.PT CertificateChecks.KernelSpor.M24Syl.ptM

namespace CertificateChecks.KernelSpor.M24Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.KS.SporSch.MOC CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch

set_option maxRecDepth 100000

@[expose] def ES : List (List Int) := m24SylowExprs

#kw_list CertificateChecks.KernelSpor.M24Syl.pTr
  (exprsV 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES) 128
#kw_list CertificateChecks.KernelSpor.M24Syl.pTir
  (exprsI 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES) 128
#kw_list CertificateChecks.KernelSpor.M24Syl.Er
  (MSylF.clRunQ 24 5 (mask 5) pTr 1100 (nat_lit 0) ([I], MSylF.bucketsOfS [I], [I], [])).1.reverse
  128

theorem s_pT : MSylF.eqNL (exprsV 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES)
    pTr = true := by
  quickRfl

theorem s_pTi : MSylF.eqNL (exprsI 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES)
    pTir = true := by
  quickRfl

theorem s_E : MSylF.eqNL (MSylF.clRunQ 24 5 (mask 5) pTr 1100 (nat_lit 0)
    ([I], MSylF.bucketsOfS [I], [I], [])).1.reverse Er = true := by
  quickRfl

theorem s_1 : Nat.beq (pcomp 24 5 (mask 5) A Ai) I = true := by quickRfl

theorem s_2 : Nat.beq (pcomp 24 5 (mask 5) B Bi) I = true := by quickRfl

theorem s_3 : Nat.beq (pcomp 24 5 (mask 5) Z Zi) I = true := by quickRfl

theorem s_4 : allL (fun e => allL (fun g =>
    CFSG.KC.NatBuckets.memB (MSylF.bucketsOfS Er) (pcomp 24 5 (mask 5) e g)) pTr) Er =
    true := by
  quickRfl

theorem s_5 : allL (fun e => allL (fun g =>
    CFSG.KC.NatBuckets.memB (MSylF.bucketsOfS Er) (pcomp 24 5 (mask 5) e g)) pTir) Er =
    true := by
  quickRfl

theorem s_6 : distB Er = true := by quickRfl

theorem s_7 : Nat.beq Er.length (Nat.shiftLeft (nat_lit 1) 10) = true := by quickRfl

theorem s_8 : Nat.beq (Nat.mod 244823040 (Nat.shiftLeft (nat_lit 1) 10)) (nat_lit 0) = true := by
  quickRfl

theorem s_9 : Nat.beq (Nat.mod (Nat.div 244823040 (Nat.shiftLeft (nat_lit 1) 10)) (nat_lit 2))
    (nat_lit 1) = true := by
  quickRfl

theorem s_10 : memB A Er = true := by quickRfl

theorem s_11 : memB Z Er = true := by quickRfl

theorem s_12 : commAllP 24 5 (mask 5) Z pTr = true := by quickRfl

theorem syl : sylowAutP 24 5 (mask 5) I A Ai B Bi m24Derivs ES Z Zi 1100 244823040 10 = true :=
  MSylF.sylowAutP_of (MSylF.eq_of_eqNL s_pT) (MSylF.eq_of_eqNL s_pTi)
    ((MSylF.closP_eqQ _ _ _ _ _ _).trans (MSylF.eq_of_eqNL s_E)) s_1 s_2 s_3 (MSylF.closedP_of s_4)
    (MSylF.closedP_of s_5) s_6 s_7 s_8 s_9 s_10 s_11 s_12

theorem pt : (exprsV 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES == PT) = true := by
  quickRfl

theorem scan : Nat.beq (enumFrom 24 5 (mask 5) (24 * 5) M24C1.LR M24C1.TR
    (centBadP 24 5 (mask 5) (pidn 24 5) Z PT) 3 0 (pidn 24 5) 0) 0 = true := by
  quickRfl

theorem zb : (!Nat.beq (pcomp 24 5 (mask 5) Z B) (pcomp 24 5 (mask 5) B Z)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.M24Syl

end
