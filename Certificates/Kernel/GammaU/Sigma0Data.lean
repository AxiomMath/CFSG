module

public import Certificates.Data.Kernel.GammaUSigmaK
public import Certificates.Data.Kernel.IdxFourSiftK
public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUS0 "Certificates/Kernel/GammaU/data/sig0.json.gz" 67116
  15049707100465346917 (B : List Nat) (O : List Nat) (SP : Nat) (SI : Nat) (WD : List (List Nat))
  (TL : List (List Nat)) (T : List Nat) (PS : List Nat) (TR : List (List (List Nat)))
  (R : List (List (List Nat))) (QP : List (List Nat)) (RW : List (List Nat))
  (DW : List (List Nat)) (NI : Nat) (OL : List Nat) (OT : List (List Nat)) (C : Nat) (CG : Nat)

namespace CFSG.KD.GUS0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU.SigmaP CFSG.GF2Type.Smith1979.GammaU.ResPair

@[expose] noncomputable def NG : List Nat := (n2Gens 0).map packR

@[expose] noncomputable def PG : List Nat := pgP NG NI (commPairs 0)

@[expose] noncomputable def PI : List Nat := pgI NG NI (commPairs 0)

@[expose] noncomputable def TG : List Nat :=
  targets NG NI (commPairs 0) (packR CFSG.GF2Type.Smith1979.GammaU.SigmaP.thetaRows) C

@[expose] noncomputable def blk (i c : Nat) : Bool := blkOK SP T O TL R i c

@[expose] noncomputable def lvl (i : Nat) : Bool :=
  cntOK O TL R i && treeOK SP T O TL TR i && posOK T O PS B i

@[expose] noncomputable def gens : Bool :=
  tlOK SP B TL 11 1 && tlOK SP B TL 11 2 && tlOK SP B TL 11 3 && tlOK SP B TL 11 4 &&
    invOK SP SI 11 && wordsOK SP SI 11 WD 2

end CFSG.KD.GUS0

end
