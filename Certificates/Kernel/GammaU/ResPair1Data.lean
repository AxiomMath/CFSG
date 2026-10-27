module

public import Certificates.Kernel.GammaU.Pair1Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GURP1 "Certificates/Kernel/GammaU/data/rp1.json.gz" 858
  8470279461571931761 (RT : List Nat) (RW : List (List (List Nat)))

namespace CFSG.KD.GURP1

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KD.GUT1 CFSG.KD.GUP1

@[expose] noncomputable def letR (j : Nat) : Nat → Nat :=
  letT N2 NN (nthD 0 N2) (nthD 0 RC j) (nthD 0 RCI j)

@[expose] noncomputable def rp (j : Nat) : Bool :=
  bif Nat.beq (nthD 0 RT j) 0 then
    d2aOK L CFSG.KD.GUC1.TH (letR (Nat.add j 1)) (Nat.add NN NN) (nthD [] RW j)
  else Nat.beq (nthD 0 RT j) 1 && d1OK L (letR (Nat.add j 1)) (Nat.add NN NN) (nthD [] RW j)

@[expose] noncomputable def lists : Bool := Nat.beq (lenN RT) 29 && Nat.beq (lenN RW) 29

end CFSG.KD.GURP1

end
