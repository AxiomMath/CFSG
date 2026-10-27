module

public import Certificates.Data.Kernel.ThCensus.Words
public import Certificates.Kernel.ThCensus.Data
public import Certificates.Kernel.ThCensus.WordData
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const

public section

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCensus CFSG.KD.ThCensus CFSG.KD.ThCensusW

@[expose] noncomputable def ch17305F (k : Nat) : Bool :=
  fusOK RB PW CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE regX1 regX2 reps tgts (fus.getD k [])
    (WD k)

@[expose] noncomputable def ch17305C (j : Nat) : Bool :=
  cenOK RB PW CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE regB2 regZ regS regU (tgts.getD j [])
    (cen.getD j []) (WD (Nat.add (nat_lit 50) j))

end CertificateChecks.KernelThCensus

end
