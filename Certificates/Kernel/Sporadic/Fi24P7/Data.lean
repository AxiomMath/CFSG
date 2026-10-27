module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK
public import Certificates.Kernel.Sporadic.Fi24G2e.Data
public import Certificates.Data.Kernel.Spor.Fi24P7
public import Certificates.Data.Kernel.Spor.Fi24G2d
public import Certificates.Data.Kernel.Spor.Fi24Kn

#kc_repo #kc_json_gz CFSG.KD.Fi24P7.J "Certificates/Kernel/Sporadic/Fi24P7/data/p7.json.gz" 3554
  14721811698819982941
  (A0 : List Nat) (A2 : List Nat) (A4 : List Nat) (B0 : List Nat) (B4 : List Nat)
  (BASE : List Nat) (CA2 : List (List Nat)) (CA4 : List (List Nat)) (CB4 : List (List Nat))
  (CS4 : List (List Nat)) (K0 : List Nat) (K1 : List Nat) (K2 : List Nat) (K3 : List Nat)
  (K4 : List Nat) (MBASE : List Nat) (R0 : Nat) (R2 : Nat) (R4 : Nat) (S0 : List Nat)
  (S1 : List Nat) (S2 : List Nat) (S3 : List Nat) (S4 : List Nat) (T2 : List Nat)
#kc_repo #kc_ktree_gz CFSG.KD.Fi24P7 TB "Certificates/Kernel/Sporadic/Fi24P7/data/p7tab.bin.gz" 2560 4 706560 5316288289543475481
#kc_repo #kc_ktree_gz CFSG.KD.Fi24P7 MX "Certificates/Kernel/Sporadic/Fi24P7/data/p7mat.bin.gz" 152491 4 5642167 8290514419923597283

public section

namespace CFSG.KD.Fi24P7

@[expose] noncomputable def tv (b i : Nat) : Nat :=
  fld(TB (Nat.add b (Nat.shiftRight i (nat_lit 10))), Nat.mul (Nat.land i (nat_lit 1023)) (nat_lit 20),
    nat_lit 1048575)

@[expose] noncomputable def B2 : List Nat := J.T2 ++ J.A2 ++ J.T2

@[expose] noncomputable def F0 (i : Nat) : Nat := tv (nat_lit 0) i
@[expose] noncomputable def PA0 (i : Nat) : Nat := tv (nat_lit 4) i
@[expose] noncomputable def PB0 (i : Nat) : Nat := tv (nat_lit 8) i
@[expose] noncomputable def PAR0 (i : Nat) : Nat := tv (nat_lit 12) i
@[expose] noncomputable def DEP0 (i : Nat) : Nat := tv (nat_lit 16) i

@[expose] noncomputable def F2 (i : Nat) : Nat := tv (nat_lit 20) i
@[expose] noncomputable def PA2 (i : Nat) : Nat := tv (nat_lit 21) i
@[expose] noncomputable def PB2 (i : Nat) : Nat := tv (nat_lit 22) i
@[expose] noncomputable def Q2 (i : Nat) : Nat := tv (nat_lit 23) i
@[expose] noncomputable def QA2 (i : Nat) : Nat := tv (nat_lit 29) i
@[expose] noncomputable def QB2 (i : Nat) : Nat := tv (nat_lit 35) i
@[expose] noncomputable def QP2 (i : Nat) : Nat := tv (nat_lit 41) i
@[expose] noncomputable def QD2 (i : Nat) : Nat := tv (nat_lit 47) i

@[expose] noncomputable def F4 (i : Nat) : Nat := tv (nat_lit 53) i
@[expose] noncomputable def PA4 (i : Nat) : Nat := tv (nat_lit 54) i
@[expose] noncomputable def PB4 (i : Nat) : Nat := tv (nat_lit 55) i
@[expose] noncomputable def Q4 (i : Nat) : Nat := tv (nat_lit 56) i
@[expose] noncomputable def QA4 (i : Nat) : Nat := tv (nat_lit 100) i
@[expose] noncomputable def QB4 (i : Nat) : Nat := tv (nat_lit 144) i
@[expose] noncomputable def QP4 (i : Nat) : Nat := tv (nat_lit 188) i
@[expose] noncomputable def QD4 (i : Nat) : Nat := tv (nat_lit 232) i

end CFSG.KD.Fi24P7

end
