module

public import Certificates.Data.Kernel.Fi22.Cent
public import Certificates.Kernel.Fi22Core.ChainDefs
public import Certificates.Kernel.T46K.ChainDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.PC CFSG.KS.Fi22Cent CFSG.KS.T46K CertificateChecks.KernelFi22C
  CertificateChecks.KernelT46

@[expose] noncomputable def rrK (l : Nat) : List Nat :=
  mapK (fun u => PHK (EPK (LJ l (EAK (PIK u))))) QT

@[expose] noncomputable def lvChk (l : Nat) : Bool :=
  bAnd(allN (nat_lit 693) fun i => Nat.blt (EPK (LJ l (EAK i))) (nat_lit 693),
    siftF LK POST PART LABT CNTT BT QT (nat_lit 5) (nat_lit 0) (rrK l))

@[expose] noncomputable def rs (s : Nat) : Bool := rowSl s

@[expose] noncomputable def lvSl (t : Nat) : Bool := lvChk (lvAt LJ BJ (nat_lit 32) (nat_lit 1) t)

end CertificateChecks.KernelFi22Cent

end
