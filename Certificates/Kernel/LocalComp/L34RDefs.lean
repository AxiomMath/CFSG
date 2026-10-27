module

public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Kernel.LocalComp.L34WData

public section

namespace CertificateChecks.KernelLC

open CFSG.KC.L34K CertificateChecks.KernelLC.L34X

@[expose] noncomputable def L34O.T (o j : Nat) : Nat :=
  nIf(Nat.beq o (nat_lit 0), at8 L34O0.TP (nat_lit 252) j,
    nIf(Nat.beq o (nat_lit 1), at8 L34O1.TP (nat_lit 252) j,
      nIf(Nat.beq o (nat_lit 2), at8 L34O2.TP (nat_lit 252) j, at8 L34O3.TP (nat_lit 252) j)))

@[expose] noncomputable def L34O.N (o : Nat) : Nat :=
  nIf(Nat.beq o (nat_lit 0), nat_lit 315, nIf(Nat.beq o (nat_lit 1), nat_lit 360,
    nIf(Nat.beq o (nat_lit 2), nat_lit 1008, nat_lit 280)))

@[expose] noncomputable def L34R.pr (s : Nat) : Bool :=
  pinSl 42 6 6 L34R.G L34R.T L34R.E L34R.C L34R.S L34R.SI 241920 1344 18 s

@[expose] noncomputable def L34R.rp (s : Nat) : Bool :=
  rPassSl 42 6 L34R.G L34R.T L34O.T L34O.N L34W.W 1344 s

end CertificateChecks.KernelLC

end
