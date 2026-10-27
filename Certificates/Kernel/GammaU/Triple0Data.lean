module

public import Certificates.Kernel.GammaU.Census0Data
public import Certificates.Data.Kernel.GammaUViolK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUT0 "Certificates/Kernel/GammaU/data/tri0.json.gz" 6435
  18186968638707020480 (N2 : List Nat) (NN : Nat) (NLG : Nat) (NLGI : Nat) (HM : List Nat)
  (UM : List Nat) (CW : List (List Nat)) (CWI : List (List Nat)) (CC : Nat) (CCi : Nat)
  (XA : List Nat) (WT : List (List (List Nat)))

namespace CFSG.KD.GUT0

open CFSG.KC.IF4C CFSG.KC.GUC CFSG.KC.GUV

@[expose] noncomputable def L : List Nat := five CFSG.KD.GUC0.CG 0

@[expose] noncomputable def let0 (X q : Nat) : Nat → Nat :=
  letT N2 NN (candL CFSG.KD.GUC0.CG CFSG.KD.GUC0.FT CFSG.KD.GUC0.FTi CFSG.KD.GUC0.FC
    CFSG.KD.GUC0.TH 0 X) (look CC q) (look CCi q)

@[expose] noncomputable def tri (x q : Nat) : Bool :=
  d2aOK L CFSG.KD.GUC0.TH (let0 (nthD 0 XA x) q) (NN + 11) (nthD [] WT (Nat.add (Nat.mul 12 x) q))

@[expose] noncomputable def cj (q : Nat) : Bool :=
  ltAll 6 (nthD [] CW q) && Nat.beq (wordP NLG NLGI (nthD [] CW q)) (look CC q) &&
    Nat.beq (wordP NLG NLGI (nthD [] CWI q)) (look CCi q) &&
    cjOK L CFSG.KD.GUC0.S0 (nthD 0 UM q) (look CC q) (look CCi q)

@[expose] noncomputable def lists : Bool :=
  Nat.beq (lenN UM) 12 && Nat.beq (lenN XA) 12 && ltAll 384 XA && Nat.beq (lenN WT) 144 &&
    Nat.beq NN (lenN N2) &&
    allBelow 32 (fun m => !(unitP CFSG.KD.GUC0.TH (subQ L m)) || Nat.beq m 0 || memN m UM ||
      memN m HM) &&
    allBelow 384 (fun X => !(Nat.beq (fld CFSG.KD.GUC0.LB X) CFSG.KD.GUC0.AR) || memN X XA)

end CFSG.KD.GUT0

end
