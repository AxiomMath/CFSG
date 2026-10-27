module

public import Certificates.Kernel.EvenSporCo0.Data
public import Certificates.Data.Kernel.EvenSporCo0.Eighth
public import CFSG.Certificates.Kernel.Spor.RawDefs
public meta import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelCo0

open CFSG.KC.EvenSporCo0 CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def gensK : Bool :=
  Nat.beq sylowGens.size 10 &&
    (List.range 10).all fun k => sylowGens[k]! == CFSG.KS.Raw.unpack 24 5 (S.G k)

theorem gensK_true : gensK = true := by decide +kernel

theorem edgesOK : edgesK 10 S.N S.G S.T S.E = true := by decide +kernel

theorem replayOK' : replayK 10 S.N S.E = true := by decide +kernel

theorem N_eq : S.N = 1024 := by decide +kernel

@[expose] noncomputable def blk (j : ℕ) : Bool := eighthBlk S.T (64 * j) 64

end CertificateChecks.KernelCo0

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelCo0.blk 0 16

end
