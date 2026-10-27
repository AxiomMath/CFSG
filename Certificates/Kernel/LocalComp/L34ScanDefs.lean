module

public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Data.Kernel.L34Scan

public section

namespace CertificateChecks.KernelLC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Scan
open CertificateChecks.KernelLC.L34X

@[expose] noncomputable def two1 (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => scanSl (twoK 42 6 64 L34C1.P e) L34R.T 1344 s

@[expose] noncomputable def fix2 (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 1) fun r =>
    scanSl (fixK 42 6 r 168 L34C2.P e) L34R.T 1344 s

@[expose] noncomputable def fix3 (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 2) fun r =>
    scanSl (fixK 42 6 r 60 L34C3.P e) L34R.T 1344 s

end CertificateChecks.KernelLC.L34Scan

end
