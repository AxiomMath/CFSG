module

public import Certificates.Kernel.Fi22Guest.Data
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneFi22CentData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22E9

open CFSG.KC.Enum CFSG.KS CFSG.KS.Row CertificateChecks.KernelFi22Guest
  CFSG.LocalAnalysis.RankThreeUC.AGL81C.Fi22Cent

@[expose] noncomputable def sComp (l : List Int) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) y (fun s _ ih => strictN ih fun z => lmap s z) l

@[expose] noncomputable def cent3Chk : Bool :=
  allN (nat_lit 3510) fun x => bAnd(Nat.beq (iterK (sComp uData) (nat_lit 3) x) x,
    Nat.beq (iterK (sComp vData) (nat_lit 3) x) x)

@[expose] noncomputable def centCommChk : Bool :=
  allN (nat_lit 3510) fun x =>
    bAnd(Nat.beq (sComp uData (sComp vData x)) (sComp vData (sComp uData x)),
      bAnd(Nat.beq (sComp uData (qMap iC x)) (qMap iC (sComp uData x)),
        Nat.beq (sComp vData (qMap jC x)) (qMap jC (sComp vData x))))

@[expose] noncomputable def centProd (t y : Nat) : Nat :=
  iterK (sComp uData) (Nat.div t (nat_lit 3)) (iterK (sComp vData) (Nat.mod t (nat_lit 3)) y)

@[expose] noncomputable def centProdChk : Bool :=
  allN (nat_lit 8) fun t => movesK (centProd (Nat.succ t))

@[expose] noncomputable def centQMvChk : Bool :=
  bAnd(movesK (qMap iC), movesK (qMap jC))

end CertificateChecks.KernelFi22E9

end
