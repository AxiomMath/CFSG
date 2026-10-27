module

public import Certificates.Data.Kernel.Spor.MSylowCent
public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Derivs
public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Inputs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutM23Inputs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutM23Derivs
public meta import CFSG.Sporadic.Schreier.M23Gens
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M23Syl

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m23PermA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m23PermB).toArray

meta def tZM : Array Nat := CFSG.Sporadic.Schreier.m23SylowZ.toArray

meta def tAiM : Array Nat := invA tAM

meta def tBiM : Array Nat := invA tBM

meta def tZiM : Array Nat := invA tZM

meta def oneM : Array Nat := idA 23

meta def ptM : Array Nat :=
  (CFSG.Sporadic.Schreier.m23SylowExprs.map fun e =>
    CFSG.KS.RawGen.pack 5 (evalW 23 (strongOf 23 #[tAM, tBM] CFSG.Sporadic.Schreier.m23Derivs) e)).toArray

end CertificateChecks.KernelSpor.M23Syl

#ks_perm CertificateChecks.KernelSpor.M23Syl.I 5 CertificateChecks.KernelSpor.M23Syl.oneM
#ks_perm CertificateChecks.KernelSpor.M23Syl.A 5 CertificateChecks.KernelSpor.M23Syl.tAM
#ks_perm CertificateChecks.KernelSpor.M23Syl.Ai 5 CertificateChecks.KernelSpor.M23Syl.tAiM
#ks_perm CertificateChecks.KernelSpor.M23Syl.B 5 CertificateChecks.KernelSpor.M23Syl.tBM
#ks_perm CertificateChecks.KernelSpor.M23Syl.Bi 5 CertificateChecks.KernelSpor.M23Syl.tBiM
#ks_perm CertificateChecks.KernelSpor.M23Syl.Z 5 CertificateChecks.KernelSpor.M23Syl.tZM
#ks_perm CertificateChecks.KernelSpor.M23Syl.Zi 5 CertificateChecks.KernelSpor.M23Syl.tZiM
#kss_list CertificateChecks.KernelSpor.M23Syl.PT CertificateChecks.KernelSpor.M23Syl.ptM

namespace CertificateChecks.KernelSpor.M23Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.KS.SporSch.MOC CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch

set_option maxRecDepth 100000

@[expose] def ES : List (List Int) := m23SylowExprs

theorem syl : sylowAutP 23 5 (mask 5) I A Ai B Bi m23Derivs ES Z Zi 150 10200960 7 = true := by
  quickRfl

theorem pt : (exprsV 23 5 (mask 5) I (slpP 23 5 (mask 5) I A Ai B Bi m23Derivs) ES == PT) = true := by
  quickRfl

theorem scan : Nat.beq (enumFrom 23 5 (mask 5) (23 * 5) M23C1.LR M23C1.TR
    (centBadP 23 5 (mask 5) (pidn 23 5) Z PT) 4 0 (pidn 23 5) 0) 0 = true := by
  quickRfl

theorem zb : (!Nat.beq (pcomp 23 5 (mask 5) Z B) (pcomp 23 5 (mask 5) B Z)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.M23Syl

end
