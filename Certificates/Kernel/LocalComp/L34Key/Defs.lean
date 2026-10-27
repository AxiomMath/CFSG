module

public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Data.Kernel.L34Key
public import Certificates.Data.Kernel.L34Scan

public section

namespace CertificateChecks.KernelLC.L34Key

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Scan CFSG.KC.L34Key
open CertificateChecks.KernelLC.L34X

@[expose] noncomputable def ci9304 (c : Nat) : Nat := pinvS 42 6 (mask 6) (L34C1.P c)

@[expose] noncomputable def key9304 (s : Nat) : Bool :=
  strictB (RP 0) fun r => scanSl (keyK 42 6 64 L34C1.P r) L34R.T 1344 s

end CertificateChecks.KernelLC.L34Key

end
