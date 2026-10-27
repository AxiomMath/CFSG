module

public import Certificates.Kernel.MaxD2.McLP.Enum
public import Certificates.Kernel.MaxD2.McLP.Data
public import Certificates.Data.Kernel.MaxD2.Heis
public import Certificates.Data.Kernel.MaxD2.Pair

public section

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

@[expose] noncomputable def repsK (lo m : Nat) : Bool :=
  allN m (fun d => repK 275 9 2 18 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H (Nat.add lo d))

@[expose] noncomputable def commsK (lo m : Nat) : Bool :=
  allN m (fun d => allN (Nat.succ (Nat.add lo d)) (fun l =>
    commK 275 9 RE.cnt 5 RE.T (r32 ZP) (r32 CZ) (Nat.add lo d) l))

@[expose] noncomputable def pairsK (c : Nat) : Bool :=
  allN 36 (fun d => strictB (Nat.add (Nat.mul 36 c) d) (fun q =>
    pairK 275 9 2 18 NE.cnt (r32 PT) NE.T FS KS REP REPI RB2 H2 q (r32 PI q) (r32 PJ q)))

end CertificateChecks.KernelMaxD2.McLP

end
