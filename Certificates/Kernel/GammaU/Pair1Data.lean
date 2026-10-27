module

public import Certificates.Kernel.GammaU.Triple1Data
public import Certificates.Data.Kernel.GammaUPairK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUP1 "Certificates/Kernel/GammaU/data/pair1.json.gz" 4173
  15791364755004879142 (PM : List Nat) (PW : List (List Nat)) (PWI : List (List Nat)) (PC : Nat)
  (PCi : Nat) (RP : List Nat) (DR : List Nat) (DW : List (List (List Nat))) (TG : List Nat)
  (WP : List (List (List Nat))) (RC : List Nat) (RCI : List Nat)

namespace CFSG.KD.GUP1

open CFSG.KC.IF4C CFSG.KC.GUC CFSG.KC.GUV CFSG.KD.GUT1

@[expose] noncomputable def cand (x : Nat) : Nat → Nat :=
  candL CFSG.KD.GUC1.CG CFSG.KD.GUC1.FT CFSG.KD.GUC1.FTi CFSG.KD.GUC1.FC CFSG.KD.GUC1.TH 1
    (nthD 0 XA x)

@[expose] noncomputable def letQ (k d₁ d₂ : Nat) : Nat → Nat :=
  letP (cand (nthD 0 RP d₁)) (cand (nthD 0 RP d₂)) (look PC (Nat.mul 2 k))
    (look PCi (Nat.mul 2 k)) (look PC (Nat.add (Nat.mul 2 k) 1)) (look PCi (Nat.add (Nat.mul 2 k) 1))
    CFSG.KD.GUC1.TH

@[expose] noncomputable def pair (k d₁ d₂ : Nat) : Bool :=
  pairW L CFSG.KD.GUC1.TH N2 NN (letQ k d₁ d₂) RC RCI
    (nthD 0 TG (Nat.add (Nat.mul 2 (Nat.add (Nat.mul 2 k) d₁)) d₂))
    (nthD [] WP (Nat.add (Nat.mul 2 (Nat.add (Nat.mul 2 k) d₁)) d₂))

@[expose] noncomputable def row (x : Nat) : Bool := allBelow 2 (pair (Nat.div x 2) (Nat.mod x 2))

@[expose] noncomputable def pcj (j : Nat) : Bool :=
  ltAll 6 (nthD [] PW j) && Nat.beq (wordP NLG NLGI (nthD [] PW j)) (look PC j) &&
    Nat.beq (wordP NLG NLGI (nthD [] PWI j)) (look PCi j) &&
    cjOK L CFSG.KD.GUC1.S0 (nthD 0 PM j) (look PC j) (look PCi j)

@[expose] noncomputable def dup (x : Nat) : Bool :=
  Nat.blt (nthD 0 DR x) 2 && dupOK (cand (nthD 0 RP (nthD 0 DR x))) (cand x) (nthD [] DW x)

@[expose] noncomputable def lists : Bool :=
  Nat.beq (lenN PM) 4 && Nat.beq (lenN RP) 2 && ltAll 4 RP && Nat.beq (lenN DR) 4 &&
    Nat.beq (lenN TG) 8 && Nat.beq (lenN WP) 8 && Nat.beq (lenN RCI) (lenN RC) &&
    allBelow 4 (fun x => Nat.beq (fld CFSG.KD.GUC1.LB (nthD 0 XA x)) CFSG.KD.GUC1.AR)

end CFSG.KD.GUP1

end
