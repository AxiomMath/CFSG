module

public import Certificates.Kernel.HSStd.U43VbData
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.MulHF
public import Certificates.Data.Kernel.Spor.PEnumRC
public import Certificates.Data.Kernel.U43Case

public section

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelHSStd

@[expose] noncomputable def GJC (j : Nat) : Nat := VbI (Nat.add j 2)

@[expose] noncomputable def GJY (j : Nat) : Nat := VbI (Nat.add j 7)

@[expose] noncomputable def peT (s : Nat) : Bool :=
  slK VbKT.cnt (CFSG.KS.PEnumRC.recPtK 820 10 (mask 10) VbKT.G VbKT.GI 4 VbKT.T VbKT.PL)
    (Nat.mul 126 s) 126

@[expose] noncomputable def hsT (s : Nat) : Bool :=
  slK VbKT.cnt (hsortPtKF 820 10 (mask 10) VbKT.cnt VbKT.T VbKT.HS VbKT.HSI) (Nat.mul 567 s) 567

@[expose] noncomputable def peK (s : Nat) : Bool :=
  slK VbKY.cnt (CFSG.KS.PEnumRC.recPtK 820 10 (mask 10) VbKY.G VbKY.GI 4 VbKY.T VbKY.PL)
    (Nat.mul 112 s) 112

@[expose] noncomputable def hsK (s : Nat) : Bool :=
  slK VbKY.cnt (hsortPtKF 820 10 (mask 10) VbKY.cnt VbKY.T VbKY.HS VbKY.HSI) (Nat.mul 840 s) 840

@[expose] noncomputable def cv (s : Nat) : Bool :=
  coverP 820 10 VbC.cnt VbC.T VbCY.cnt VbCY.T VbW (Nat.mul 360 s) 360

end CertificateChecks.KernelHSStd.U43Vb

end
