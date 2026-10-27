module

public import Certificates.Kernel.Sporadic.ONNQ.Tabs
public import Certificates.Kernel.Sporadic.ONNQ.Data
public import Certificates.Data.Kernel.Spor.ONNQK

public section

namespace CertificateChecks.KernelSpor.ONNQ

open CFSG.KS.ONNQ

@[expose] noncomputable def nqFoS (s : Nat) : Bool :=
  fstRange TT UU ONQ.D ONQ.FR (nat_lit 122760) (Nat.mul s (nat_lit 1240)) (nat_lit 1240)

@[expose] noncomputable def nqCoS (s : Nat) : Bool :=
  cosRange TT UU ONQ.D (nat_lit 58818) (Nat.mul s (nat_lit 57)) (nat_lit 57)

@[expose] noncomputable def nqWiS (s : Nat) : Bool :=
  witRange TT UU ONQ.D (nat_lit 58818) (Nat.mul s (nat_lit 120)) (nat_lit 120)

@[expose] noncomputable def nqHead : Bool := headOK TT UU ONQ.D (nat_lit 58818)

end CertificateChecks.KernelSpor.ONNQ

end
