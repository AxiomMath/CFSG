module

public import Certificates.Kernel.Sporadic.ON.Data
public import CFSG.Certificates.Kernel.Spor.PackWord
public import Certificates.Data.Kernel.Spor.ONVecK
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native

meta def packV (v : V) : Nat := v.p ||| (v.m <<< 256)

meta def orbO : VOrbit := vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)

meta def formM : Array V := rowsOf 154 CFSG.ONSchreier.Data.formPayload

meta def cmM : List Nat := (transpose 154 formM).toList.map packV

meta def xiM : List Nat := (transpose 154 (invV 154 formM)).toList.map packV

meta def raM : List Nat := (rowsA ()).toList.map packV

meta def rbM : List Nat := (rowsB ()).toList.map packV

meta def cuM : List Nat :=
  (transpose 154 (toVM (spanRows orbO CFSG.ONSchreier.Data.spanIdx))).toList.map packV

meta def grM : List Nat := (gram orbO CFSG.ONSchreier.Data.spanIdx formM).toList.map packV

meta def blM : List Nat := CFSG.ONSchreier.Data.baseList

meta def sigT : Array W :=
  (transpose 154 (sigRows orbO formM CFSG.ONSchreier.Data.baseList)).map ofV

meta def sigO : VOrbit :=
  ⟨sigsOf orbO sigT, Array.replicate 245520 0, Array.replicate 245520 0⟩

meta def noStrong : Array (Array Nat) := #[]

meta def noWords : Array (List Int) := #[[]]

end CertificateChecks.KernelSpor.ONVec

#knatlist CertificateChecks.KernelSpor.ONVec.CM CertificateChecks.KernelSpor.ONVec.cmM
#knatlist CertificateChecks.KernelSpor.ONVec.XI CertificateChecks.KernelSpor.ONVec.xiM
#knatlist CertificateChecks.KernelSpor.ONVec.RA CertificateChecks.KernelSpor.ONVec.raM
#knatlist CertificateChecks.KernelSpor.ONVec.RB CertificateChecks.KernelSpor.ONVec.rbM
#knatlist CertificateChecks.KernelSpor.ONVec.CU CertificateChecks.KernelSpor.ONVec.cuM
#knatlist CertificateChecks.KernelSpor.ONVec.GR CertificateChecks.KernelSpor.ONVec.grM
#knatlist CertificateChecks.KernelSpor.ONVec.BL CertificateChecks.KernelSpor.ONVec.blM

#kon_data CertificateChecks.KernelSpor.ONS CertificateChecks.KernelSpor.ONVec.sigO
  CertificateChecks.KernelSpor.ONVec.noStrong CertificateChecks.KernelSpor.ONVec.sigT
  CertificateChecks.KernelSpor.ONVec.sigT CertificateChecks.KernelSpor.ONVec.noWords 240

#ks_chars CertificateChecks.KernelSpor.ONForm CFSG.ONSchreier.Data.formPayload

#ks_chars CertificateChecks.KernelSpor.ONSpanInv CFSG.ONSchreier.Data.spanInvPayload

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def at0 (L : List Nat) (j : Nat) : Nat := List.getD L j (nat_lit 0)

@[expose] noncomputable def SR (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 29), mv CM (key CertificateChecks.KernelSpor.ONV.K (at0 BL k)), nat_lit 0)

@[expose] noncomputable def sigS (s : Nat) : Bool :=
  sigRange CertificateChecks.KernelSpor.ONS.K CertificateChecks.KernelSpor.ONV.K
    CertificateChecks.KernelSpor.ONS.LA (Nat.mul s (nat_lit 240)) (nat_lit 240)

@[expose] noncomputable def ssortS (s : Nat) : Bool :=
  sortRange CertificateChecks.KernelSpor.ONS.K CertificateChecks.KernelSpor.ONS.SO
    CertificateChecks.KernelSpor.ONS.SOI (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

end CertificateChecks.KernelSpor.ONVec

end
