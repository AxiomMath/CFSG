module

public import Certificates.Kernel.UnitarySix.Sec3.K3603Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3HAElt
public import Certificates.Data.Kernel.U6.Sec3LabA1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)

@[expose] noncomputable def dD (x : ℕ) : ℕ := pg 10 (mask 10) sec3Dd x

@[expose] noncomputable def sgK (x : ℕ) : ℕ := pg 10 (mask 10) sec3Ds x

@[expose] noncomputable def dK (q x : ℕ) : ℕ :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (dD (dD (sgK x))) (dD (sgK x)) (q == 4))
    (sgK x) (q == 3)) (dD (dD x)) (q == 2)) (dD x) (q == 1)) x (q == 0)

theorem dTab_eq : ∀ x < 693, dTab[x]! = dD x := by decide +kernel
theorem sTab_eq : ∀ x < 693, sTab[x]! = sgK x := by decide +kernel
theorem dD_lt : ∀ x < 693, dD x < 693 := by decide +kernel
theorem sgK_lt : ∀ x < 693, sgK x < 693 := by decide +kernel

@[expose] noncomputable def labK (x : ℕ) : ℕ := pg 10 (mask 10) sec3LabA1 x

theorem labA1_eq : ∀ x < 693, labA1[x]! = labK x := by decide +kernel

@[expose] noncomputable def c10WK (L : List ℕ) (q : ℕ) : Bool :=
  (List.range 9).any fun j => !(allN 693 fun p =>
    strictB (pg 10 (mask 10) (CA1.S j) (ptL 10 (mask 10) L (dK q p))) fun r =>
    strictB (ptL 10 (mask 10) L (dK q (pg 10 (mask 10) (CA1.S j) p))) fun l =>
      l == r || l == pg 10 (mask 10) (sec3G 14) r)

@[expose] noncomputable def c8WK (L : List ℕ) (q : ℕ) : Bool :=
  (List.range 5).any fun j => !(allN 693 fun p =>
    labK (ptL 10 (mask 10) L (dK q (pg 10 (mask 10) (CK1.S j) p))) ==
      labK (pg 10 (mask 10) (CK1.S j) (ptL 10 (mask 10) L (dK q p))))

@[expose] noncomputable def anyWL (W : List (List ℕ)) (y x : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun w _ ih => y == ptW w x || ih) W

@[expose] noncomputable def c11RK (L : List ℕ) : Bool :=
  (List.range 3).any fun j => !(allN 693 fun p =>
    strictB (ptL 10 (mask 10) L p) fun x =>
      anyWL z2sW (ptL 10 (mask 10) L (pg 10 (mask 10) (CZ2S.S j) p)) x)

@[expose] noncomputable def k3606L (L : List ℕ) : Bool :=
  (allN 6 fun q => c10WK L q || (q == 0 && strictB (prodL 693 10 (mask 10) L) isId)) &&
  (allN 6 fun q => q == 1 || q == 2 || c8WK L q ||
    (q == 0 && strictB (prodL 693 10 (mask 10) L) isId)) &&
  (c11RK L || strictB (prodL 693 10 (mask 10) L) sfP2)

theorem chZ2S_P : ∀ j < chZ2S.gens.length, PermK (CZ2S.S j) (CZ2S.SI j) = true := by
  decide +kernel

@[expose] def z2sKeysLit : List ℕ := [1, 43, 13, 2, 28, 29, 44, 14]

theorem kZ2SKeys : (z2sW.map fun w => ptW w 1) = z2sKeysLit := by decide +kernel

@[expose] noncomputable def z2sKeyL (L : List ℕ) : Bool :=
  (ptL 10 (mask 10) L 1 != 1 || strictB (prodL 693 10 (mask 10) L) isId) &&
    memL (ptL 10 (mask 10) L 1) z2sKeysLit

theorem kLabA1 : ((List.range chA1.gens.length).all fun j => allN 693 fun p =>
    labK (pg 10 (mask 10) (CA1.S j) p) == labK p) = true := by
  decide +kernel

@[expose] noncomputable def k3606Run (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CK1.LR CK1.TR k3606L 2 1
    [CK1.TR (roff 693 (693 * 10) (CK1.LR 0) + (lo + j))]

theorem k3606_all (h : ∀ s < 30, k3606Run (s * 4) 4 = true) :
    prodLazyK 693 (693 * 10) CK1.LR CK1.TR k3606L 3 0 [] = true :=
  loop_of_blocks (N := 30) (B := 4) (by decide +kernel) h

@[expose] noncomputable def z2sRunK : Bool := prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR z2sKeyL 1 0 []

end CertificateChecks.KernelU6.Sec3
