module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.LocalComp.HeFixWordsData
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeFix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] noncomputable def RT (j : Nat) : Nat → Nat :=
  [XR, C0R, C1R, C2R, C3R, C4R, C5R, C6R, C7R, C8R].getD j XR

@[expose] noncomputable def WJ (j : Nat) : List Int :=
  Nat.rec (motive := fun _ => List Int) hfXWord (fun k _ => heInnerWords1.getD k []) j

@[expose] noncomputable def SJ (j : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) LU (fun _ _ => L3) j

@[expose] noncomputable def SIJ (j : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) LUI (fun _ _ => L3I) j

@[expose] noncomputable def FJ (j : Nat) : Nat := Nat.rec (motive := fun _ => Nat) PX (fun k _ => PC1 k) j

@[expose] noncomputable def NB (j : Nat) : Nat := [15, 1, 1, 1, 4, 1, 1, 1, 7, 6].getD j 0

@[expose] noncomputable def ckW (j i : Nat) : Bool :=
  Nat.beq (wordK 8330 14 (mask 14) (RT j (i + 1)) (SJ j) (SIJ j) (((WJ j).drop (32 * i)).take 32))
    (RT j i)

@[expose] noncomputable def enK (j : Nat) : Bool :=
  ((Nat.beq (RT j (NB j)) (pidn 8330 14) && Nat.ble (WJ j).length (32 * NB j)) &&
    (szOK 8330 14 && lettersK 3 (WJ j))) && Nat.beq (RT j 0) (FJ j)

@[expose] noncomputable def ck0 (i : Nat) : Bool := ckW 0 i
@[expose] noncomputable def ck1 (i : Nat) : Bool := ckW 1 i
@[expose] noncomputable def ck2 (i : Nat) : Bool := ckW 2 i
@[expose] noncomputable def ck3 (i : Nat) : Bool := ckW 3 i
@[expose] noncomputable def ck4 (i : Nat) : Bool := ckW 4 i
@[expose] noncomputable def ck5 (i : Nat) : Bool := ckW 5 i
@[expose] noncomputable def ck6 (i : Nat) : Bool := ckW 6 i
@[expose] noncomputable def ck7 (i : Nat) : Bool := ckW 7 i
@[expose] noncomputable def ck8 (i : Nat) : Bool := ckW 8 i
@[expose] noncomputable def ck9 (i : Nat) : Bool := ckW 9 i

end CertificateChecks.KernelLC.HeFix

#kon_slices CertificateChecks.KernelLC.HeFix.ck0 0 15
#kon_join CertificateChecks.KernelLC.HeFix.ck0All CertificateChecks.KernelLC.HeFix.ck0 15
#kon_slices CertificateChecks.KernelLC.HeFix.ck1 0 1
#kon_join CertificateChecks.KernelLC.HeFix.ck1All CertificateChecks.KernelLC.HeFix.ck1 1
#kon_slices CertificateChecks.KernelLC.HeFix.ck2 0 1
#kon_join CertificateChecks.KernelLC.HeFix.ck2All CertificateChecks.KernelLC.HeFix.ck2 1
#kon_slices CertificateChecks.KernelLC.HeFix.ck3 0 1
#kon_join CertificateChecks.KernelLC.HeFix.ck3All CertificateChecks.KernelLC.HeFix.ck3 1
#kon_slices CertificateChecks.KernelLC.HeFix.ck4 0 4
#kon_join CertificateChecks.KernelLC.HeFix.ck4All CertificateChecks.KernelLC.HeFix.ck4 4
#kon_slices CertificateChecks.KernelLC.HeFix.ck5 0 1
#kon_join CertificateChecks.KernelLC.HeFix.ck5All CertificateChecks.KernelLC.HeFix.ck5 1
#kon_slices CertificateChecks.KernelLC.HeFix.ck6 0 1
#kon_join CertificateChecks.KernelLC.HeFix.ck6All CertificateChecks.KernelLC.HeFix.ck6 1
#kon_slices CertificateChecks.KernelLC.HeFix.ck7 0 1
#kon_join CertificateChecks.KernelLC.HeFix.ck7All CertificateChecks.KernelLC.HeFix.ck7 1
#kon_slices CertificateChecks.KernelLC.HeFix.ck8 0 7
#kon_join CertificateChecks.KernelLC.HeFix.ck8All CertificateChecks.KernelLC.HeFix.ck8 7
#kon_slices CertificateChecks.KernelLC.HeFix.ck9 0 6
#kon_join CertificateChecks.KernelLC.HeFix.ck9All CertificateChecks.KernelLC.HeFix.ck9 6
#kon_slices CertificateChecks.KernelLC.HeFix.enK 0 10
#kon_join CertificateChecks.KernelLC.HeFix.enAll CertificateChecks.KernelLC.HeFix.enK 10

end
