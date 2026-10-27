module

public import Certificates.Kernel.Sporadic.OddCore.SuzRT
public import Certificates.Kernel.Sporadic.OddCore.SuzRK
public import Certificates.Kernel.Sporadic.OddCore.SuzMGF
public import Certificates.Kernel.Sporadic.L2.Defs
public import Certificates.Kernel.Sporadic.L2.Defs2
public import Certificates.Data.Kernel.Spor.CEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzRTK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KS.CEnum CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.L2K CertificateChecks.KernelSpor.OddCore

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Idn" => pidn 1782 11

@[expose] noncomputable def XT : Nat := SuzRTX.F 0
@[expose] noncomputable def XTI : Nat := SuzRTI 0
@[expose] noncomputable def YT : Nat := SuzRTY.F 0
@[expose] noncomputable def YTI : Nat := SuzRTI 1
@[expose] noncomputable def T1P : Nat := SuzTP 1
@[expose] noncomputable def AP : Nat := L2A 342
@[expose] noncomputable def VR : Nat := TK 135 0
@[expose] noncomputable def VR' : Nat := TK 55 0
@[expose] noncomputable def V1 : Nat := pc RHO (pc VR RHOI)
@[expose] noncomputable def V1' : Nat := pc RHO (pc VR' RHOI)
@[expose] noncomputable def W0R : Nat := pc RHO (pc W0 RHOI)

@[expose] noncomputable def cmK (G H : Nat) : Bool := Nat.beq (pc G H) (pc H G)

@[expose] noncomputable def inVK (V V₁ Z : Nat) : Bool :=
  Nat.beq Z V || Nat.beq Z V₁ || Nat.beq Z (pc V V₁)

@[expose] noncomputable def normVK (V V₁ G GI : Nat) : Bool :=
  inVK V V₁ (pc G (pc V GI)) && inVK V V₁ (pc G (pc V₁ GI))

@[expose] noncomputable def baseK : Bool :=
  cn XT && cn XTI && cn YT && cn YTI && ie XT XTI && ie YT YTI && msift XT && msift YT &&
    msift (SuzRKG 0) && msift (SuzRKG 1)

@[expose] noncomputable def commK : Bool :=
  cmK RHO T1P && cmK RHO AP && cmK XT T1P && cmK XT AP && cmK YT T1P && cmK YT AP

@[expose] noncomputable def normK : Bool :=
  normVK VR V1 RHO RHOI && normVK VR V1 XT XTI && normVK VR' V1' RHO RHOI &&
    normVK VR' V1' YT YTI

@[expose] noncomputable def sqK : Bool :=
  Nat.beq (SuzMGF.powK RHO 3) Idn && Nat.beq (SuzMGF.powK (pc XT YT) 2) Idn &&
    !Nat.beq (SuzMGF.powK (pc XT (pc RHO (pc YT RHOI))) 2) Idn &&
    ie (SuzMGF.powK RHO 2) (SuzMGF.powK RHOI 2) &&
    !Nat.beq (SuzMGF.powK (pc XT (pc (SuzMGF.powK RHO 2) (pc YT (SuzMGF.powK RHOI 2)))) 2) Idn

@[expose] noncomputable def evenK : Bool :=
  cmK (pc XT RHOI) VR && cmK (pc XT RHOI) V1 && cmK (pc YT RHO) VR' && cmK (pc YT RHO) V1'

@[expose] noncomputable def kGenK : Bool :=
  cmK (SuzRKG 0) T1P && cmK (SuzRKG 1) T1P && cmK (SuzRKG 0) RHO && cmK (SuzRKG 1) RHO

theorem kBase : baseK = true := by quickRfl
theorem kComm : commK = true := by quickRfl
theorem kNorm : normK = true := by quickRfl
theorem kSq : sqK = true := by quickRfl
theorem kEven : evenK = true := by quickRfl
theorem kKGen : kGenK = true := by quickRfl

theorem neg_inv : Bool.not (ie XT YTI) = true := by quickRfl

theorem neg_comm : Bool.not (cmK XT RHO) = true := by quickRfl

@[expose] noncomputable def cHdK : Bool :=
  cenumHdK 1782 11 (mask 11) (1782 * 11) 2 960 Idn RHO SuzMGG SuzMGGI SuzRCT SuzRCFP

@[expose] noncomputable def cSl (s : Nat) : Bool :=
  cenumSlK 1782 11 (mask 11) (1782 * 11) 2 960 RHO SuzMGG SuzMGGI SuzRCT SuzRCTI SuzRCPL SuzRCPOS
    SuzRCFP SuzRCSRT SuzRCSRI (Nat.mul (nat_lit 80) s) (nat_lit 80)

theorem kCHd : cHdK = true := by quickRfl

theorem neg_class : Bool.not (cenumPtK 1782 11 (mask 11) (1782 * 11) 2 960 RHO SuzMGG SuzMGGI
    SuzRCT SuzRCTI (fun i => Nat.add (SuzRCPL i) (nat_lit 2)) SuzRCPOS SuzRCFP SuzRCSRT SuzRCSRI
    5) = true := by
  quickRfl

theorem neg_classFp : Bool.not (cenumPtK 1782 11 (mask 11) (1782 * 11) 2 960 RHO SuzMGG SuzMGGI
    SuzRCT SuzRCTI SuzRCPL SuzRCPOS (fun i => Nat.add (SuzRCFP i) (nat_lit 1)) SuzRCSRT SuzRCSRI
    3) = true := by
  quickRfl

@[expose] noncomputable def oT (o i : Nat) : Nat := pg 12 (mask 12) (SuzROT o) i
@[expose] noncomputable def oPL (o i : Nat) : Nat := pg 15 (mask 15) (SuzROPL o) i
@[expose] noncomputable def oPOS (o e : Nat) : Nat := pg 12 (mask 12) (SuzROPOS o) e
@[expose] noncomputable def oVP (o v : Nat) : Nat := pg 12 (mask 12) (SuzROVP o) v

@[expose] noncomputable def actK (G GI v y : Nat) : Bool :=
  bIf(Nat.blt v 2835, bAnd(Nat.blt y 2835, Nat.beq (fA y) (fpCK 11 (mask 11) G GI (L2A v))),
    bAnd(Nat.ble 2835 v, bAnd(Nat.blt v 2997, bAnd(Nat.ble 2835 y, bAnd(Nat.blt y 2997,
      strictB (fpCK 11 (mask 11) G GI (TK (Nat.sub v 2835) 0)) fun f =>
      strictB (Nat.mul 3 (Nat.sub y 2835)) fun b =>
        bIf(Nat.beq (fT b) f, true, bIf(Nat.beq (fT (Nat.add b 1)) f, true,
          Nat.beq (fT (Nat.add b 2)) f)))))))

@[expose] noncomputable def oHd (o b cnt : Nat) : Bool :=
  bAnd(Nat.beq (oT o 0) b, Nat.blt 0 cnt)

@[expose] noncomputable def oPt (o off cnt i : Nat) : Bool :=
  strictB (oT o i) fun v =>
  bAnd(Nat.blt v 2997, bAnd(Nat.beq (oVP o v) i,
  bAnd(bIf(Nat.beq i 0, true, strictB (oPL o i) fun c =>
    bAnd(Nat.blt (Nat.div c 6) i, bAnd(Nat.beq (oPOS o c) i,
      bIf(Nat.blt (Nat.succ i) cnt, Nat.blt c (oPL o (Nat.succ i)), true)))),
  allN 6 fun s => strictB (oPOS o (Nat.add (Nat.mul 6 i) s)) fun q =>
    bAnd(Nat.blt q cnt, bAnd(actK (L2EL.F (Nat.add off s)) (L2EI (Nat.add off s)) v (oT o q),
      bIf(Nat.beq q 0, true, Nat.ble (oPL o q) (Nat.add (Nat.mul 6 i) s)))))))

theorem kOrbP : bAnd(oHd 0 2835 18, allN 18 (oPt 0 0 18)) = true := by quickRfl

theorem kOrbQ : bAnd(oHd 1 0 315, allN 315 (oPt 1 6 315)) = true := by quickRfl

theorem neg_orb : Bool.not (actK (L2EL.F 0) (L2EI 0) 2835 (Nat.succ (oT 0 (oPOS 0 0)))) = true := by
  quickRfl

@[expose] noncomputable def eltK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) Idn (fun a _ ih => pc (L2EL.F a) ih) l

@[expose] noncomputable def eltIK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) Idn (fun a _ ih => pc ih (L2EI a)) l

@[expose] noncomputable def evenAtK (M a : Nat) : Bool :=
  cmK (pc M (SuzMGF.powK RHOI a)) W0 && cmK (pc M (SuzMGF.powK RHOI a)) W0R

@[expose] noncomputable def plusBK (M MI : Nat) : Bool :=
  ie M MI && cmK M T1P && normVK W0 W0R M MI && (evenAtK M 0 || evenAtK M 1 || evenAtK M 2)

@[expose] noncomputable def squareK (v X XI : Nat) (ph pk : List Nat) (y : Nat) : Bool :=
  strictB (eltK ph) fun H => strictB (eltIK ph) fun HI =>
  strictB (pc H (eltK pk)) fun U => strictB (pc (eltIK pk) HI) fun UI =>
    ie H HI && memXK H && sendsK H HI 0 0 && sendsK H HI 2835 v && actK HI H 342 y &&
      ie U UI && memXK U && sendsK U UI 0 342 && sendsK U UI 2835 v &&
      plusBK (pc HI (pc X H)) (pc HI (pc XI H)) && plusBK (pc UI (pc X U)) (pc UI (pc XI U))

@[expose] noncomputable def pathK : Bool :=
  Nat.beq (oT 0 11) 2970 && Nat.beq (oPL 0 11) (6 * 3 + 4) && Nat.beq (oPL 0 3) (6 * 0 + 3) &&
    Nat.beq (oT 0 2) 2890 && Nat.beq (oPL 0 2) (6 * 0 + 2) &&
    Nat.beq (oT 1 61) 1436 && Nat.beq (oPL 1 61) (6 * 10 + 2) && Nat.beq (oPL 1 10) (6 * 1 + 3) &&
    Nat.beq (oPL 1 1) (6 * 0 + 0) &&
    Nat.beq (oT 1 53) 1660 && Nat.beq (oPL 1 53) (6 * 8 + 5) && Nat.beq (oPL 1 8) (6 * 1 + 1)

theorem kPath : pathK = true := by quickRfl

theorem kSqV : squareK 2970 XT XTI [4, 3] [8, 9, 6] 1436 = true := by quickRfl

theorem kSqV' : squareK 2890 YT YTI [2] [11, 7, 6] 1660 = true := by quickRfl

theorem neg_sq : Bool.not (squareK 2970 XT XTI [2] [8, 9, 6] 1436) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzRTK

end
