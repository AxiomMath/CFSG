module

public import Certificates.Kernel.GammaU.Triple0Data
public import Certificates.Data.Kernel.GammaUPairK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUP0 "Certificates/Kernel/GammaU/data/pair0.json.gz" 6427
  13121232366442443093 (PM : List Nat) (PW : List (List Nat)) (PWI : List (List Nat)) (PC : Nat)
  (PCi : Nat) (RP : List Nat) (DR : List Nat) (DW : List (List (List Nat))) (TG : List Nat)
  (WP : List (List (List Nat))) (RC : List Nat) (RCI : List Nat)

namespace CFSG.KD.GUP0

open CFSG.KC.IF4C CFSG.KC.GUC CFSG.KC.GUV CFSG.KD.GUT0

@[expose] noncomputable def cand (x : Nat) : Nat → Nat :=
  candL CFSG.KD.GUC0.CG CFSG.KD.GUC0.FT CFSG.KD.GUC0.FTi CFSG.KD.GUC0.FC CFSG.KD.GUC0.TH 0
    (nthD 0 XA x)

@[expose] noncomputable def letQ (k d₁ d₂ : Nat) : Nat → Nat :=
  letP (cand (nthD 0 RP d₁)) (cand (nthD 0 RP d₂)) (look PC (Nat.mul 2 k))
    (look PCi (Nat.mul 2 k)) (look PC (Nat.add (Nat.mul 2 k) 1)) (look PCi (Nat.add (Nat.mul 2 k) 1))
    CFSG.KD.GUC0.TH

@[expose] noncomputable def pair (k d₁ d₂ : Nat) : Bool :=
  pairW L CFSG.KD.GUC0.TH N2 NN (letQ k d₁ d₂) RC RCI
    (nthD 0 TG (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 6 k) d₁)) d₂))
    (nthD [] WP (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 6 k) d₁)) d₂))

@[expose] noncomputable def row (x : Nat) : Bool := allBelow 6 (pair (Nat.div x 6) (Nat.mod x 6))

@[expose] noncomputable def pcj (j : Nat) : Bool :=
  ltAll 6 (nthD [] PW j) && Nat.beq (wordP NLG NLGI (nthD [] PW j)) (look PC j) &&
    Nat.beq (wordP NLG NLGI (nthD [] PWI j)) (look PCi j) &&
    cjOK L CFSG.KD.GUC0.S0 (nthD 0 PM j) (look PC j) (look PCi j)

@[expose] noncomputable def dup (x : Nat) : Bool :=
  Nat.blt (nthD 0 DR x) 6 && dupOK (cand (nthD 0 RP (nthD 0 DR x))) (cand x) (nthD [] DW x)

@[expose] noncomputable def lists : Bool :=
  Nat.beq (lenN PM) 4 && Nat.beq (lenN RP) 6 && ltAll 12 RP && Nat.beq (lenN DR) 12 &&
    Nat.beq (lenN TG) 72 && Nat.beq (lenN WP) 72 && Nat.beq (lenN RCI) (lenN RC) &&
    allBelow 12 (fun x => Nat.beq (fld CFSG.KD.GUC0.LB (nthD 0 XA x)) CFSG.KD.GUC0.AR)

end CFSG.KD.GUP0

end
