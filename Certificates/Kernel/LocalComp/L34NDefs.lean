module

public import Certificates.Kernel.LocalComp.L34NData
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Data.Kernel.L34Norm

public section

namespace CertificateChecks.KernelLC.L34N

open CFSG.KC.Enum CFSG.KC.L34Norm

@[expose] noncomputable def code (e k : Nat) : Nat :=
  normCode (nat_lit 42) (nat_lit 6) (nat_lit 9) AP (K (nat_lit 0)) (K (nat_lit 1)) (K (nat_lit 2))
    (nat_lit 1) (nat_lit 27) e (L34R.T k)

@[expose] noncomputable def l34n (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => curSl (code e) J 1344 C s

end CertificateChecks.KernelLC.L34N

end
