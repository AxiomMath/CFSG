module

public import Certificates.Data.Kernel.O8.Frame
public import Certificates.Kernel.OmegaEight.SA3002K
public import Certificates.Kernel.O8Frame9490.Chain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameData

public section

namespace CertificateChecks.KernelO8F

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.KC.O8F CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
open CFSG.EvenSmallLie.OmegaEightMinus (bNat)

@[expose] noncomputable def BK (i : Nat) : Nat := J.S i

@[expose] noncomputable def CK : Nat := T.S 3

@[expose] noncomputable def TauK : Nat := packA 136 8 tauArr

@[expose] noncomputable def SK : Nat := packA 136 8 sArr

@[expose] noncomputable def NGK (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) SK TauK (Nat.beq i 1)) CK
    (Nat.beq i 0)

@[expose] noncomputable def sixK (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pinvM (BK (Nat.div k 2))) (BK (Nat.div k 2))
    (Nat.beq (Nat.mod k 2) 0)

@[expose] noncomputable def ZK : Nat := pcM (pcM (BK 0) (BK 1)) (BK 2)

@[expose] noncomputable def siftOm (x : Nat) : Bool :=
  siftK 136 8 (mask 8) (136 * 8) (pidn 136 8) OmM.LR OmM.TRI OmM.BP 7 0 x

@[expose] noncomputable def siftJ (x : Nat) : Bool :=
  siftK 136 8 (mask 8) (136 * 8) (pidn 136 8) J.LR J.TRI J.BP 3 0 x

@[expose] noncomputable def okK (x : Nat) : Bool := bAnd(cnM x, bAnd(pmM x, cnM (pinvM x)))

@[expose] noncomputable def suppK (x : Nat) : Nat :=
  (List.range 136).countP fun i => !(Nat.beq (at8 x i) i)

@[expose] noncomputable def trJ (i k : Nat) : Nat := J.TR (Nat.add (roff 136 (136 * 8) (J.LR i)) k)

@[expose] noncomputable def x3 (a b c : Nat) : Nat := pcM (pcM (trJ 0 a) (trJ 1 b)) (trJ 2 c)

@[expose] noncomputable def nWK (w : List Nat) : Nat := w.foldr (fun i acc => pcM (NGK i) acc) pidM

@[expose] noncomputable def pickGoK (x : Nat) :
    List (List Nat) → List Nat → List (List Nat) → List (List Nat)
  | [], _, acc => acc.reverse
  | w :: ws, seen, acc =>
    if acc.length = 4 then acc.reverse else
      if seen.any (fun y' => Nat.beq (cjM (nWK w) x) y' || Nat.beq (cjM (nWK w) x) (pinvM y'))
      then pickGoK x ws seen acc else pickGoK x ws (cjM (nWK w) x :: seen) (w :: acc)

@[expose] noncomputable def sepK (x : Nat) (ws : List (List Nat)) : Bool :=
  ws.length == 4 && ws.all (fun w => w.all fun i => decide (i < 3)) &&
    allN 4 fun k => allN 4 fun l => Nat.beq k l ||
    (!(Nat.beq (cjM (nWK ws[k]!) x) (cjM (nWK ws[l]!) x)) &&
      !(Nat.beq (cjM (nWK ws[k]!) x) (cjM (nWK ws[l]!) (pinvM x))))

@[expose] def psiCodeT (l : List Nat) (v : Nat) : Nat :=
  v ^^^ psiIota (psiCoord v) ^^^ psiIota (permBitsT l (psiCoord v))

@[expose] noncomputable def psiK (l : List Nat) : Nat := fnK NSM NIM (psiCodeT l)

@[expose] noncomputable def notSixK (x : Nat) : Bool :=
  (List.range 6).all fun k => !(Nat.beq x (sixK k))

@[expose] noncomputable def eltK (a b c : Nat) : Bool :=
  strictB (x3 a b c) fun x =>
  bAnd(okK x, bAnd(Nat.beq (pcM x (pcM x x)) pidM,
  bAnd(allN 3 (fun a' => allN 3 fun b' => allN 3 fun c' =>
    Nat.beq (pcM x (x3 a' b' c')) (pcM (x3 a' b' c') x)),
  bAnd(Bool.rec (motive := fun _ => Bool) (notSixK x) (!(notSixK x)) (Nat.beq (suppK x) 108),
  bAnd(!(Nat.beq (pcM x CK) (pcM CK x)) || Nat.beq x pidM || Nat.beq x ZK || Nat.beq x (pinvM ZK),
  bAnd(candWords.all (fun w => okK (cjM (nWK w) x)),
    Nat.beq x pidM || Nat.beq (suppK x) 108 || sepK x (pickGoK x candWords [] [])))))))

@[expose] noncomputable def rtK (l : List Nat) (i : Nat) : Bool :=
  strictB (psiCodeT l (CFSG.KLie.CT.fget NSM i 8)) fun w =>
  bAnd(Nat.blt (CFSG.KLie.CT.fget NIM w 8) 136,
  bAnd(Nat.beq (CFSG.KLie.CT.fget NSM (CFSG.KLie.CT.fget NIM w 8) 8) w,
    Nat.beq (psiCoord w) (permBitsT l (psiCoord (CFSG.KLie.CT.fget NSM i 8)))))

@[expose] noncomputable def psiOK (l : List Nat) : Bool :=
  strictB (psiK l) fun p =>
  bAnd(fnLtK NSM (psiCodeT l), bAnd(okK p, bAnd(Nat.beq (pcM p (BK 0)) (pcM (BK 0) p),
  bAnd(bIf(decide (sgnT l = 1), siftOm p, true), allN 136 (rtK l)))))

end CertificateChecks.KernelO8F

end
