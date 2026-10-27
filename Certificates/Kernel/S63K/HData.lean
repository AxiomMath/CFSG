module

public import CFSG.Certificates.Kernel.Th.S.Chars
public import Certificates.Data.D4HexBase
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#th_chars CertificateChecks.KernelS63.HD.PC CFSG.D4Hex.permText
#th_chars CertificateChecks.KernelS63.HD.LC CFSG.D4Hex.lineText

#kc_repo #kc_ktree CertificateChecks.KernelS63.HD TX "Certificates/Kernel/S63K/data/hperm.bin" 11057 4 121627 2951652398420080404
#kc_repo #kc_ktree CertificateChecks.KernelS63.HD T "Certificates/Kernel/S63K/data/hmat.bin" 72 4 2359656 12987959458822375727

namespace CertificateChecks.KernelS63.HD

@[expose] noncomputable def PA (j : Nat) : Nat := TX j
@[expose] noncomputable def LT : Nat := TX 8
@[expose] noncomputable def DP : Nat := TX 9
@[expose] noncomputable def DL : Nat := TX 10
@[expose] noncomputable def G3 : Nat := T 0
@[expose] noncomputable def UG (l : Nat) : Nat := T (1 + l)
@[expose] noncomputable def TP (i : Nat) : Nat := T (5 + i)
@[expose] noncomputable def TPar (i : Nat) : Nat := T (4101 + i)
@[expose] noncomputable def TLab (i : Nat) : Nat := T (8197 + i)
@[expose] noncomputable def TW (i : Nat) : Nat := T (12293 + i)
@[expose] noncomputable def TS (i : Nat) : Nat := T (28677 + i)

end CertificateChecks.KernelS63.HD

end
