module

public import Certificates.Kernel.SchreierFam.He725S
public import Certificates.Kernel.SchreierFam.He725W
public import Certificates.Kernel.SchreierFam.He725D
public import Certificates.Kernel.LocalComp.HeFix
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.He725

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def RT (j : Nat) : Nat → Nat := [R0, R1, R2, R3, R4, R5].getD j R0

@[expose] noncomputable def WJ (j : Nat) : List Int :=
  [gL.getD 0 [], cL.getD 0 [], qL.getD 0 [], qL.getD 1 [], qL.getD 2 [], qL.getD 3 []].getD j []

@[expose] noncomputable def FJ (j : Nat) : Nat :=
  [He725S.S 0, CC 0, QQ 0, QQ 1, QQ 2, QQ 3].getD j 0

@[expose] noncomputable def NB (j : Nat) : Nat := [14, 7, 1, 4, 3, 4].getD j 0

@[expose] noncomputable def ckW (j i : Nat) : Bool :=
  Nat.beq (wordK 8330 14 (mask 14) (RT j (i + 1)) LU LUI (((WJ j).drop (32 * i)).take 32))
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

end CertificateChecks.KernelSchreierFam.He725

#kon_slices CertificateChecks.KernelSchreierFam.He725.ck0 0 14
#kon_join CertificateChecks.KernelSchreierFam.He725.ck0All CertificateChecks.KernelSchreierFam.He725.ck0 14
#kon_slices CertificateChecks.KernelSchreierFam.He725.ck1 0 7
#kon_join CertificateChecks.KernelSchreierFam.He725.ck1All CertificateChecks.KernelSchreierFam.He725.ck1 7
#kon_slices CertificateChecks.KernelSchreierFam.He725.ck2 0 1
#kon_join CertificateChecks.KernelSchreierFam.He725.ck2All CertificateChecks.KernelSchreierFam.He725.ck2 1
#kon_slices CertificateChecks.KernelSchreierFam.He725.ck3 0 4
#kon_join CertificateChecks.KernelSchreierFam.He725.ck3All CertificateChecks.KernelSchreierFam.He725.ck3 4
#kon_slices CertificateChecks.KernelSchreierFam.He725.ck4 0 3
#kon_join CertificateChecks.KernelSchreierFam.He725.ck4All CertificateChecks.KernelSchreierFam.He725.ck4 3
#kon_slices CertificateChecks.KernelSchreierFam.He725.ck5 0 4
#kon_join CertificateChecks.KernelSchreierFam.He725.ck5All CertificateChecks.KernelSchreierFam.He725.ck5 4
#kon_slices CertificateChecks.KernelSchreierFam.He725.enK 0 6
#kon_join CertificateChecks.KernelSchreierFam.He725.enAll CertificateChecks.KernelSchreierFam.He725.enK 6

end
