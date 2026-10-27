module

public import Certificates.Data.Kernel.Spor.MSylowCent
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

theorem syl : sylowAutP 24 5 (mask 5) I A Ai B Bi m24Derivs ES Z Zi 1100 244823040 10 = true := by
  quickRfl

theorem pt : (exprsV 24 5 (mask 5) I (slpP 24 5 (mask 5) I A Ai B Bi m24Derivs) ES == PT) = true := by
  quickRfl

theorem scan : Nat.beq (enumFrom 24 5 (mask 5) (24 * 5) M24C1.LR M24C1.TR
    (centBadP 24 5 (mask 5) (pidn 24 5) Z PT) 3 0 (pidn 24 5) 0) 0 = true := by
  quickRfl

theorem zb : (!Nat.beq (pcomp 24 5 (mask 5) Z B) (pcomp 24 5 (mask 5) B Z)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.M24Syl

end
