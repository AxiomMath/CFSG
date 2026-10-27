module

public import Certificates.Kernel.GammaU.Pair1Data
public import Certificates.Data.Kernel.GammaUNormK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUN1 "Certificates/Kernel/GammaU/data/nl1.json.gz" 22822
  10561826453768729658 (UQ : List Nat) (NM : List Nat) (CV : List (List (List Nat)))
  (RW : List (List (List Nat)))

namespace CFSG.KD.GUN1

open CFSG.KC.IF4C CFSG.KC.GUC CFSG.KC.GUV
open CFSG.KD.GUT1 (L NLG NLGI N2 NN)
open CFSG.KD.GUP1 (PM RC RCI)

@[expose] noncomputable def D0K : List Nat := [961, 48, 9, 5, 3, 3072]

@[expose] noncomputable def letN (e : Nat) : Nat :=
  bif Nat.beq (Nat.mod e 2) 0 then look NLG (Nat.div e 2) else look NLGI (Nat.div e 2)

@[expose] noncomputable def nl (e : Nat) : Bool :=
  nlP L CFSG.KD.GUC1.TH D0K (CFSG.GF2Type.Smith1979.GammaU.spanList D0K) (letN e)
    (fun m => nthD 0 NM (Nat.add (Nat.mul 32 e) m))

@[expose] noncomputable def cv (p : Nat) : Bool :=
  allBelow 15 fun q => Nat.beq p q ||
    cvOK L NLG NLGI PM (nthD 0 UQ p) (nthD 0 UQ q) (nthD [] CV (Nat.add (Nat.mul 15 p) q))

@[expose] noncomputable def rp (e : Nat) : Bool :=
  allBelow 30 fun c => rpOK N2 NN RC RCI (letN e) c (nthD [] RW (Nat.add (Nat.mul 30 e) c))

@[expose] noncomputable def lists : Bool :=
  Nat.beq (lenN UQ) 15 && ltAll 32 UQ &&
    allBelow 32 (fun m => !(unitP CFSG.KD.GUC1.TH (subQ L m)) || Nat.beq m 0 || memN m UQ) &&
    Nat.beq (lenN RC) 30 && allBelow 30 fun c => Nat.beq (mulP (nthD 0 RC c) (nthD 0 RCI c)) idP

end CFSG.KD.GUN1

end
