module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_ktree CertificateChecks.KernelS63.PD T "Certificates/Kernel/S63K/data/pdata.bin" 72 4 4193568 2918637514842076597

namespace CertificateChecks.KernelS63.PD

@[expose] noncomputable def SW (j : Nat) : Nat := T j
@[expose] noncomputable def SV (j : Nat) : Nat := T (12 + j)
@[expose] noncomputable def U0 (_ : Nat) : Nat := T 24
@[expose] noncomputable def FO (i : Nat) : Nat := T (25 + i)
@[expose] noncomputable def FPa (i : Nat) : Nat := T (520 + i)
@[expose] noncomputable def FLa (i : Nat) : Nat := T (1015 + i)
@[expose] noncomputable def FW (i : Nat) : Nat := T (1510 + i)
@[expose] noncomputable def FS (i : Nat) : Nat := T (7450 + i)
@[expose] noncomputable def FI (i : Nat) : Nat := T (7945 + i)
@[expose] noncomputable def QA (i : Nat) : Nat := T (12041 + i)
@[expose] noncomputable def QB (i : Nat) : Nat := T (14505 + i)
@[expose] noncomputable def QPa (i : Nat) : Nat := T (16969 + i)
@[expose] noncomputable def QLa (i : Nat) : Nat := T (19433 + i)
@[expose] noncomputable def QW (i : Nat) : Nat := T (21897 + i)
@[expose] noncomputable def QS (i : Nat) : Nat := T (51465 + i)
@[expose] noncomputable def QK (_ : Nat) : Nat := T 53929
@[expose] noncomputable def ZCP (i : Nat) : Nat := T (53930 + i)
@[expose] noncomputable def ZCPar (i : Nat) : Nat := T (53933 + i)
@[expose] noncomputable def ZCLab (i : Nat) : Nat := T (53936 + i)
@[expose] noncomputable def ZCW (i : Nat) : Nat := T (53939 + i)
@[expose] noncomputable def ZCS (i : Nat) : Nat := T (53951 + i)
@[expose] noncomputable def UCP (i : Nat) : Nat := T (53954 + i)
@[expose] noncomputable def UCPar (i : Nat) : Nat := T (53978 + i)
@[expose] noncomputable def UCLab (i : Nat) : Nat := T (54002 + i)
@[expose] noncomputable def UCW (i : Nat) : Nat := T (54026 + i)
@[expose] noncomputable def UCS (i : Nat) : Nat := T (54122 + i)
@[expose] noncomputable def TI (i : Nat) : Nat := T (54146 + i)
@[expose] noncomputable def VC (_ : Nat) : Nat := T 58242
@[expose] noncomputable def PW (_ : Nat) : Nat := T 58243

end CertificateChecks.KernelS63.PD

end
