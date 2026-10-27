module

public import Certificates.Data.Kernel.Spor.MSylow
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Derivs
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Inputs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutM22Inputs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutM22Derivs
public meta import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m22gA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m22gB).toArray

meta def tZM : Array Nat := CFSG.Sporadic.Schreier.m22SylowZ.toArray

meta def tAiM : Array Nat := invA tAM

meta def tBiM : Array Nat := invA tBM

meta def tZiM : Array Nat := invA tZM

meta def tZBM : Array Nat := comp tZM (comp tBM tZiM)

meta def oneM : Array Nat := idA 22

meta def ptM : Array Nat :=
  (CFSG.Sporadic.Schreier.m22SylowExprs.map fun e =>
    CFSG.KS.RawGen.pack 5 (evalW 22 (strongOf 22 #[tAM, tBM] CFSG.Sporadic.Schreier.m22Derivs) e)).toArray

meta def lvM (i : Nat) : Array Nat :=
  if h : i < CFSG.Sporadic.Schreier.m22Certificate.baseCount then
    ((CFSG.Sporadic.Schreier.levelTransversals CFSG.Sporadic.Schreier.m22Certificate ⟨i, h⟩).map
      fun t => CFSG.KS.RawGen.pack 5 (CFSG.Monster.B.Mathieu.imageList t).toArray).toArray
  else #[]

meta def L0M : Array Nat := lvM 0
meta def L1M : Array Nat := lvM 1
meta def L2M : Array Nat := lvM 2
meta def L3M : Array Nat := lvM 3
meta def L4M : Array Nat := lvM 4

end CertificateChecks.KernelSpor.M22Syl

#ks_perm CertificateChecks.KernelSpor.M22Syl.I 5 CertificateChecks.KernelSpor.M22Syl.oneM
#ks_perm CertificateChecks.KernelSpor.M22Syl.A 5 CertificateChecks.KernelSpor.M22Syl.tAM
#ks_perm CertificateChecks.KernelSpor.M22Syl.Ai 5 CertificateChecks.KernelSpor.M22Syl.tAiM
#ks_perm CertificateChecks.KernelSpor.M22Syl.B 5 CertificateChecks.KernelSpor.M22Syl.tBM
#ks_perm CertificateChecks.KernelSpor.M22Syl.Bi 5 CertificateChecks.KernelSpor.M22Syl.tBiM
#ks_perm CertificateChecks.KernelSpor.M22Syl.Z 5 CertificateChecks.KernelSpor.M22Syl.tZM
#ks_perm CertificateChecks.KernelSpor.M22Syl.Zi 5 CertificateChecks.KernelSpor.M22Syl.tZiM
#ks_perm CertificateChecks.KernelSpor.M22Syl.ZB 5 CertificateChecks.KernelSpor.M22Syl.tZBM
#kss_list CertificateChecks.KernelSpor.M22Syl.PT CertificateChecks.KernelSpor.M22Syl.ptM
#kss_list CertificateChecks.KernelSpor.M22Syl.L0 CertificateChecks.KernelSpor.M22Syl.L0M
#kss_list CertificateChecks.KernelSpor.M22Syl.L1 CertificateChecks.KernelSpor.M22Syl.L1M
#kss_list CertificateChecks.KernelSpor.M22Syl.L2 CertificateChecks.KernelSpor.M22Syl.L2M
#kss_list CertificateChecks.KernelSpor.M22Syl.L3 CertificateChecks.KernelSpor.M22Syl.L3M
#kss_list CertificateChecks.KernelSpor.M22Syl.L4 CertificateChecks.KernelSpor.M22Syl.L4M

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier

set_option maxRecDepth 100000

@[expose] def ES : List (List Int) := m22SylowExprs

@[expose] noncomputable def cnt (t : Nat) : Nat :=
  pcnt 22 5 (mask 5) (survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4)
    [[t], L1, L2, L3, L4] I 0

theorem syl : sylowAutP 22 5 (mask 5) I A Ai B Bi m22Derivs ES Z Zi 150 443520 7 = true := by
  quickRfl

theorem pt : (exprsV 22 5 (mask 5) I (slpP 22 5 (mask 5) I A Ai B Bi m22Derivs) ES == PT) = true := by
  quickRfl

@[expose] noncomputable def chunkOK (k : Nat) : Bool :=
  allL (fun t => Nat.beq (cnt t) 0) ((L0.drop (3 * k)).take 3)

end CertificateChecks.KernelSpor.M22Syl

end
