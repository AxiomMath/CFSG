module

public import Certificates.Kernel.UnitarySix.Sec3.K3607Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutElt
public import Certificates.Data.Kernel.U6.Sec3LabA4
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.EvenSmallLie.UnitarySix.YamadaHAut
open CFSG.RankThree.Native

@[expose] noncomputable def p4K (X : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) X) fun xi => PermK X xi &&
    (!((List.range 4).all fun j =>
      sfA4 (pcomp 693 10 (mask 10) X (pcomp 693 10 (mask 10) (CA4.S j) xi))) || sfP2 X)

@[expose] noncomputable def p4L (L : List ℕ) : Bool :=
  !((List.range 4).all fun j => pg 10 (mask 10) sec3LabA4
      (ptL 10 (mask 10) L (pg 10 (mask 10) (CA4.S j) 1)) == pg 10 (mask 10) sec3LabA4
      (ptL 10 (mask 10) L 1)) ||
    p4K (prodL 693 10 (mask 10) L)

theorem labA4_eq : ∀ x < 693, labA4[x]! = pg 10 (mask 10) sec3LabA4 x := by decide +kernel

theorem kLabA4 : ((List.range chA4.gens.length).all fun j => allN 693 fun p =>
    pg 10 (mask 10) sec3LabA4 (pg 10 (mask 10) (CA4.S j) p) == pg 10 (mask 10) sec3LabA4 p) =
      true := by
  decide +kernel

@[expose] noncomputable def p4Run (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CK1.LR CK1.TR p4L 2 1
    [CK1.TR (roff 693 (693 * 10) (CK1.LR 0) + (lo + j))]

theorem p4_all (h : ∀ s < 30, p4Run (s * 4) 4 = true) :
    prodLazyK 693 (693 * 10) CK1.LR CK1.TR p4L 3 0 [] = true :=
  loop_of_blocks (N := 30) (B := 4) (by decide +kernel) h

@[expose] noncomputable def commPtK (X Y : ℕ) : Bool :=
  allN 693 fun p => Nat.beq (pg 10 (mask 10) X (pg 10 (mask 10) Y p))
    (pg 10 (mask 10) Y (pg 10 (mask 10) X p))

@[expose] noncomputable def filtC (X : ℕ) (C : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun Y _ ih => Bool.rec ih (Y :: ih) (commPtK X Y)) C

@[expose] noncomputable def movesK (CS : List ℕ) (p : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun Y _ ih => pg 10 (mask 10) Y p != p || ih) CS

@[expose] noncomputable def trK (X : ℕ) : Bool :=
  (List.range 5).any fun k => strictB (wK qF[k]!) fun Q => strictB (pinvS 693 10 (mask 10) Q)
    fun QI => PermK Q QI &&
      Nat.beq X (pcomp 693 10 (mask 10) QI (pcomp 693 10 (mask 10) (sec3G 14) Q))

@[expose] noncomputable def l1K (C : List ℕ) (X : ℕ) : Bool :=
  isId X || trK X || forceL (filtC X C) [] fun CS => allN 693 fun p => movesK CS p

theorem l1W_lt : ∀ w ∈ l1Words, ∀ k ∈ w, k < 18 := by decide +kernel

@[expose] noncomputable def l1Run (a : ℕ) : Bool :=
  forceL (l1Words.map wK) [] fun CR =>
    prodLazyK 693 (693 * 10) CA4.LR CA4.TR (fun L => strictB (prodL 693 10 (mask 10) L) (l1K CR))
      1 1 [CA4.TR (roff 693 (693 * 10) (CA4.LR 0) + a)]

end CertificateChecks.KernelU6.Sec3
