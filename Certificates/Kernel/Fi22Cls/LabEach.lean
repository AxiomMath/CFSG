module

public import Certificates.Kernel.Fi22Cls.Each
public import Certificates.Kernel.Fi22Cls.LabData
public import Certificates.Kernel.Fi22S0.KillEach
public import Certificates.Data.Kernel.Fi22Cls.Lab

public section

namespace CertificateChecks.KernelFi22Cls

open CFSG.KC.Loop CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KS.Row CertificateChecks.KernelFi22S0

@[expose] noncomputable def tl (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) LF o i

@[expose] noncomputable def lab (i : Nat) : Nat := tl (nat_lit 0) i

@[expose] noncomputable def wit (i : Nat) : Nat := tl (nat_lit 616) i

@[expose] noncomputable def ch13620lab (q : Nat) : Bool :=
  blkC (nat_lit 2187)
    (labC pp pj lt wit lab rep kw kc (krep (nat_lit 0)) (nat_lit 19683) (nat_lit 126)) q

end CertificateChecks.KernelFi22Cls

end
