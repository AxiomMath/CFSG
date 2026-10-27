module

public import Certificates.Kernel.Fi22Twist.PrData
public import Certificates.Kernel.Fi22Rank.Q2Data
public import Certificates.Data.Kernel.Fi22Twist.Pairs

public section

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist

@[expose] noncomputable def ch431009px (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 729) (fun i => bAnd(qpXC CertificateChecks.KernelFi22Rank.Q2.KF PX i,
    qpOC CertificateChecks.KernelFi22Rank.Q2.KF PM PX i)) q

@[expose] noncomputable def ch431009pc (q : Nat) : Bool :=
  blkC (nat_lit 8) (nat_lit 729) (qpCC CertificateChecks.KernelFi22Rank.Q2.KF PM PX PV) q

@[expose] noncomputable def ch431009pv (q : Nat) : Bool :=
  blkC (nat_lit 8) (nat_lit 517) (qpVC CertificateChecks.KernelFi22Rank.Q2.KF PM PX PV) q

end CFSG.KD.Fi22Twist

end
