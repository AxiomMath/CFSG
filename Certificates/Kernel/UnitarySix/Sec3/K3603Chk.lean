module

public import Certificates.Kernel.UnitarySix.Sec3.E3602Chk
public import Certificates.Kernel.UnitarySix.Sec3.G3602Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3ZElt
public import Certificates.Data.Kernel.U6.Sec3Coord
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] noncomputable def pgP (x : ℕ) : ℕ := pg 10 (mask 10) sec3Pt1 x

theorem pt1_eq : ∀ x < 693, pt1Mask[x]! = pgP x := by decide +kernel

theorem pt1_lt : ∀ x < 693, pgP x < 256 := by decide +kernel

theorem wN_eq : ∀ j < 5, ∀ v < 256,
    bmulVec 8 8 (wedgeGensN.getD j #[]) v = pg 10 (mask 10) sec3WN (256 * j + v) := by
  decide +kernel

theorem wW_eq : ∀ j < 3, ∀ v < 16,
    bmulVec 4 4 (wedgeGensW.getD j #[]) v = pg 10 (mask 10) sec3WW (16 * j + v) := by
  decide +kernel

@[expose] noncomputable def kWK (x y : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun t _ ih => Bool.rec ih t.2.2 (t.1 == x && t.2.1 == y)) a4KeyTab

theorem kNGen : (pgP (pg 10 (mask 10) (pidn 693 10) 1) == 0 &&
    (List.range 256).all fun v => pgP (ptW (coordNWit v) 1) == v) = true := by
  decide +kernel

theorem kWGen : ((List.range 16).all fun v =>
    kWK (ptW (coordWWit v) 3) (ptW (coordWWit v) 1) == v) = true := by
  decide +kernel

@[expose] noncomputable def coordNL (L : List ℕ) : Bool :=
  strictB (pgP (ptL 10 (mask 10) L 1)) fun ka =>
  ((List.range 9).all fun j => pgP (ptL 10 (mask 10) L (pg 10 (mask 10) (CA1.S j) 1)) ==
    Nat.xor ka (pgP (pg 10 (mask 10) (CA1.S j) 1))) &&
  ((ka == 0) == strictB (prodL 693 10 (mask 10) L) sfZ) &&
  (List.range 5).all fun j =>
    pgP (pg 10 (mask 10) (CK1.S j) (ptL 10 (mask 10) L (pg 10 (mask 10) (CK1.SI j) 1))) ==
      pg 10 (mask 10) sec3WN (256 * j + ka)

@[expose] noncomputable def kWL (L : List ℕ) : ℕ :=
  kWK (ptL 10 (mask 10) L 3) (ptL 10 (mask 10) L 1)

@[expose] noncomputable def coordWL (L : List ℕ) : Bool :=
  strictB (kWL L) fun kw =>
  (kw != 0 || strictB (prodL 693 10 (mask 10) L) isId) &&
  (List.range 3).all fun j =>
    kWK (pg 10 (mask 10) (CLam.S j) (ptL 10 (mask 10) L (pg 10 (mask 10) (CLam.SI j) 3)))
      (pg 10 (mask 10) (CLam.S j) (ptL 10 (mask 10) L (pg 10 (mask 10) (CLam.SI j) 1))) ==
      pg 10 (mask 10) sec3WW (16 * j + kw)

@[expose] noncomputable def coordWPairL (L L' : List ℕ) : Bool :=
  kWK (ptL 10 (mask 10) L (ptL 10 (mask 10) L' 3)) (ptL 10 (mask 10) L (ptL 10 (mask 10) L' 1)) ==
    Nat.xor (kWL L) (kWL L')

@[expose] noncomputable def coordNRun (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CA1.LR CA1.TR coordNL 0 1
    [CA1.TR (roff 693 (693 * 10) (CA1.LR 0) + (lo + j))]

theorem coordN_all (h : ∀ s < 4, coordNRun (s * 128) 128 = true) :
    prodLazyK 693 (693 * 10) CA1.LR CA1.TR coordNL 1 0 [] = true :=
  loop_of_blocks (N := 4) (B := 128) (by decide +kernel) h

@[expose] noncomputable def coordWRun : Bool :=
  prodLazyK 693 (693 * 10) CA4.LR CA4.TR coordWL 2 0 [] &&
    prodLazyK 693 (693 * 10) CA4.LR CA4.TR
      (fun L => prodLazyK 693 (693 * 10) CA4.LR CA4.TR (coordWPairL L) 2 0 []) 2 0 []

end CertificateChecks.KernelU6.Sec3
