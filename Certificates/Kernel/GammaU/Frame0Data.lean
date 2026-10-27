module

public import Certificates.Kernel.GammaU.Triple0Data
public import Certificates.Kernel.GammaU.CensusCfgData
public import Certificates.Kernel.GammaU.Orb16963Data
public import Certificates.Data.Kernel.GammaUFrameCK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUFC0 "Certificates/Kernel/GammaU/data/frame0.json.gz" 63254
  8505629717836867758 (PG : List Nat) (NA : Nat) (LT : Nat) (RP : List Nat) (RJ : List Nat)
  (RW : Nat) (RWi : Nat) (SR : List (List (List (List Nat)))) (CV : List (List (List Nat)))
  (TR : List (List Nat)) (PT : Nat) (CM : List Nat)

namespace CFSG.KD.GUFC0

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUF

@[expose] noncomputable def NN2 : Nat := Nat.add CFSG.KD.GUT0.NN CFSG.KD.GUT0.NN

@[expose] noncomputable def rep (r : Nat) : Bool :=
  repOK CFSG.KD.GUC0.TH NA NN2 CFSG.KD.GUT0.HM CFSG.KD.GUCC.TB CFSG.KD.GUC0.CG LT PT CM PG
    CFSG.KD.GUCC.DT RP RJ RW RWi SR r

@[expose] noncomputable def fr (p : Nat) : Bool :=
  allBelow (lenN RP) fun r => !(Nat.beq (nthD 0 RP r) p) || rep r

@[expose] noncomputable def cv (p : Nat) : Bool := cvOK NA NN2 CFSG.KD.GUCC.DT RP RW PG CV p

@[expose] noncomputable def lists : Bool :=
  Nat.beq (lenN PG) 6 && Nat.beq (lenN CV) 6 && Nat.beq (lenN RJ) (lenN RP) &&
    Nat.beq (lenN SR) (lenN RP) && ltAll 32 CFSG.KD.GUT0.HM

end CFSG.KD.GUFC0

end
