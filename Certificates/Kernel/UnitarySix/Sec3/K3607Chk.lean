module

public import Certificates.Kernel.UnitarySix.Sec3.K3606Chk
public import Certificates.Kernel.UnitarySix.Sec3.CX3A3
public import Certificates.Kernel.UnitarySix.Sec3.CSigA3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)

@[expose] noncomputable def dPK (q : ℕ) : ℕ :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec
    (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) sec3Dd sec3Dd) sec3Ds)
    (pcomp 693 10 (mask 10) sec3Dd sec3Ds) (q == 4)) sec3Ds (q == 3))
    (pcomp 693 10 (mask 10) sec3Dd sec3Dd) (q == 2)) sec3Dd (q == 1)) (pidn 693 10) (q == 0)

theorem dPK_canon : ∀ q < 6, canonK 693 10 (mask 10) (693 * 10) (dPK q) = true := by
  decide +kernel

theorem dPK_perm : ∀ q < 6, PermK (dPK q) (pinvS 693 10 (mask 10) (dPK q)) = true := by
  decide +kernel

theorem dPK_get : ∀ q < 6, ∀ x < 693, pg 10 (mask 10) (dPK q) x = dK q x := by decide +kernel

theorem dArr_size : ∀ q < 6, (dArr[q]!).size = 693 := by decide +kernel

@[expose] noncomputable def cntK (n : ℕ) (f : ℕ → Bool) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (Bool.rec 0 1 (f i))) n

@[expose] noncomputable def c11aL (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (fun X => Nat.beq X (sec3G 14)) ||
    cntK 693 (fun p => ptL 10 (mask 10) L p == p) !=
      cntK 693 (fun p => pg 10 (mask 10) (sec3G 14) p == p)

@[expose] noncomputable def a4CommK (Y : ℕ) : Bool :=
  (List.range 4).all fun j =>
    Nat.beq (pcomp 693 10 (mask 10) Y (CA4.S j)) (pcomp 693 10 (mask 10) (CA4.S j) Y)

@[expose] noncomputable def c6L (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) fun X =>
    (!(a4CommK (pcomp 693 10 (mask 10) X (dPK 0))) || isId X) &&
      (!(a4CommK (pcomp 693 10 (mask 10) X (dPK 3))) || false)

@[expose] noncomputable def lsCommK (Y YI : ℕ) : Bool :=
  !(((List.range 3).all fun j => sfA3 (pcomp 693 10 (mask 10)
      (pcomp 693 10 (mask 10) Y (CLam.S j)) (pcomp 693 10 (mask 10) YI (CLam.SI j)))) &&
    (List.range 2).all fun j => sfA3 (pcomp 693 10 (mask 10)
      (pcomp 693 10 (mask 10) Y (CSig.S j)) (pcomp 693 10 (mask 10) YI (CSig.SI j))))

@[expose] noncomputable def dselK (q a0 a1 a2 a3 a4 a5 : ℕ) : ℕ :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec a5 a4 (q == 4)) a3 (q == 3)) a2 (q == 2)) a1
    (q == 1)) a0 (q == 0)

@[expose] noncomputable def c7PtK (X XI Z ZI DI q G GI : ℕ) : Bool :=
  fixF.any fun p => pg 10 (mask 10) X (pg 10 (mask 10) Z (dK q (pg 10 (mask 10) G
    (pg 10 (mask 10) DI (pg 10 (mask 10) ZI (pg 10 (mask 10) XI (pg 10 (mask 10) GI p))))))) != p

@[expose] noncomputable def c7K (X XI Z ZI : ℕ) (DI : ℕ → ℕ) : Bool :=
  allN 6 fun q =>
    ((List.range 3).any (fun j => c7PtK X XI Z ZI (DI q) q (CLam.S j) (CLam.SI j)) ||
      (List.range 2).any (fun j => c7PtK X XI Z ZI (DI q) q (CSig.S j) (CSig.SI j))) ||
    (isId X && isId Z && q < 3) ||
    strictB (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) X Z) (dPK q)) fun Y =>
      strictB (pinvS 693 10 (mask 10) Y) fun YI => PermK Y YI && lsCommK Y YI

@[expose] noncomputable def c9K (X : ℕ) : Bool :=
  isId X || strictB (pinvS 693 10 (mask 10) X) fun XI => PermK X XI &&
    !((List.range 2).all fun j => sfA3 (pcomp 693 10 (mask 10)
      (pcomp 693 10 (mask 10) X (CSig.S j)) (pcomp 693 10 (mask 10) XI (CSig.SI j))))

abbrev w5 : List ℕ := [16, 17, 16, 17]
abbrev w8 : List ℕ := [15, 17]

theorem perm_w58 : PermK (wK w5) (wKI w5) = true ∧ PermK (wK w8) (wKI w8) = true := by
  decide +kernel

@[expose] noncomputable def sfX3A3 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX3A3.LR CX3A3.TRI CX3A3.BP 3 0 G

@[expose] noncomputable def i5K (X : ℕ) : Bool :=
  !(sfS (pcomp 693 10 (mask 10) (wKI w5) (pcomp 693 10 (mask 10) X (wK w5)))) || sfA1 X

@[expose] noncomputable def i8K (X Y : ℕ) : Bool :=
  strictB (pcomp 693 10 (mask 10) X Y) fun P =>
    !(sfS (pcomp 693 10 (mask 10) (wKI w8) (pcomp 693 10 (mask 10) P (wK w8)))) || sfA3 P

@[expose] noncomputable def i8bK (X : ℕ) : Bool :=
  !(sfX3A3 (pcomp 693 10 (mask 10) (wKI we) (pcomp 693 10 (mask 10) X (wK we)))) || sfA3 X

theorem chX3_P : ∀ j < chX3.gens.length, PermK (CX3.S j) (CX3.SI j) = true := by decide +kernel
theorem chX3A3_P : ∀ j < chX3A3.gens.length, PermK (CX3A3.S j) (CX3A3.SI j) = true := by
  decide +kernel
theorem chP2_P : ∀ j < chP2.gens.length, PermK (CP2.S j) (CP2.SI j) = true := by decide +kernel

theorem kI5G : ((List.range chA1.gens.length).all fun j =>
    sfS (pcomp 693 10 (mask 10) (wKI w5) (pcomp 693 10 (mask 10) (CA1.S j) (wK w5)))) = true := by
  decide +kernel

theorem kI8G : ((List.range chA3.gens.length).all fun j =>
    sfS (pcomp 693 10 (mask 10) (wKI w8) (pcomp 693 10 (mask 10) (CA3.S j) (wK w8)))) &&
    ((List.range chX1.gens.length).all fun j => (List.range chX3A3.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX3A3.LR CX3A3.TRI CX3A3.BP 3 0
        (pcomp 693 10 (mask 10) (CX1.S j) (pcomp 693 10 (mask 10) (CX3A3.S i) (CX1.SI j)))) &&
    ((List.range chX3.gens.length).all fun j => (List.range chA3.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA3.LR CA3.TRI CA3.BP 2 0
        (pcomp 693 10 (mask 10) (CX3.S j) (pcomp 693 10 (mask 10) (CA3.S i) (CX3.SI j)))) =
      true := by
  decide +kernel

theorem kI8bG : ((List.range chA3.gens.length).all fun j =>
    sfX3A3 (pcomp 693 10 (mask 10) (wKI we) (pcomp 693 10 (mask 10) (CA3.S j) (wK we)))) = true := by
  decide +kernel

theorem kNM : ((List.range chA1.gens.length).all fun j => (List.range chZ2S.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CZ2S.LR CZ2S.TRI CZ2S.BP 1 0
        (pcomp 693 10 (mask 10) (CA1.S j) (pcomp 693 10 (mask 10) (CZ2S.S i) (CA1.SI j)))) &&
    ((List.range chA1.gens.length).all fun j => (List.range chA4.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA4.LR CA4.TRI CA4.BP 2 0
        (pcomp 693 10 (mask 10) (CA1.S j) (pcomp 693 10 (mask 10) (CA4.S i) (CA1.SI j)))) &&
    ((List.range chP2.gens.length).all fun j => (List.range chA4.gens.length).all fun i =>
      siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CA4.LR CA4.TRI CA4.BP 2 0
        (pcomp 693 10 (mask 10) (CP2.S j) (pcomp 693 10 (mask 10) (CA4.S i) (CP2.SI j)))) =
      true := by
  decide +kernel

@[expose] noncomputable def h3607Run : Bool :=
  prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR c11aL 1 0 [] &&
  prodLazyK 693 (693 * 10) CLam.LR CLam.TR c6L 3 0 [] &&
  prodLazyK 693 (693 * 10) CSig.LR CSig.TR (fun L => strictB (prodL 693 10 (mask 10) L) c9K)
    1 0 [] &&
  prodLazyK 693 (693 * 10) CT1.LR CT1.TR (fun L => strictB (prodL 693 10 (mask 10) L) i5K)
    2 0 [] &&
  prodLazyK 693 (693 * 10) CX1.LR CX1.TR (fun L => prodLazyK 693 (693 * 10) CX3.LR CX3.TR
    (fun L' => strictB (prodL 693 10 (mask 10) L) fun X =>
      strictB (prodL 693 10 (mask 10) L') (i8K X)) 1 0 []) 1 0 [] &&
  prodLazyK 693 (693 * 10) CX3.LR CX3.TR (fun L => strictB (prodL 693 10 (mask 10) L) i8bK) 1 0 []

@[expose] noncomputable def c7S (D0 D1 D2 D3 D4 D5 : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) fun X => strictB (pinvS 693 10 (mask 10) X) fun XI =>
    PermK X XI && prodLazyK 693 (693 * 10) CSig.LR CSig.TR (fun L' =>
      strictB (prodL 693 10 (mask 10) L') fun Z => strictB (pinvS 693 10 (mask 10) Z) fun ZI =>
        PermK Z ZI && c7K X XI Z ZI fun q => dselK q D0 D1 D2 D3 D4 D5) 1 0 []

noncomputable abbrev c7SD : List ℕ → Bool :=
  c7S (pinvS 693 10 (mask 10) (dPK 0)) (pinvS 693 10 (mask 10) (dPK 1))
    (pinvS 693 10 (mask 10) (dPK 2)) (pinvS 693 10 (mask 10) (dPK 3))
    (pinvS 693 10 (mask 10) (dPK 4)) (pinvS 693 10 (mask 10) (dPK 5))

@[expose] noncomputable def c7Run (a b : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) (dPK 0)) fun D0 => strictB (pinvS 693 10 (mask 10) (dPK 1))
    fun D1 => strictB (pinvS 693 10 (mask 10) (dPK 2)) fun D2 =>
    strictB (pinvS 693 10 (mask 10) (dPK 3)) fun D3 => strictB (pinvS 693 10 (mask 10) (dPK 4))
    fun D4 => strictB (pinvS 693 10 (mask 10) (dPK 5)) fun D5 =>
  prodLazyK 693 (693 * 10) CLam.LR CLam.TR (c7S D0 D1 D2 D3 D4 D5) 1 2
    [CLam.TR (roff 693 (693 * 10) (CLam.LR 1) + b), CLam.TR (roff 693 (693 * 10) (CLam.LR 0) + a)]

theorem cLam_sizes : rcnt (CLam.LR 0) = 5 ∧ rcnt (CLam.LR 1) = 4 := by decide +kernel

theorem c7_all (h : ∀ a < 5, ∀ b < 4, c7Run a b = true) :
    prodLazyK 693 (693 * 10) CLam.LR CLam.TR c7SD 3 0 [] = true := by
  rw [prodLazyK_succ, cLam_sizes.1]
  refine allN_of_forall₀ fun a ha => ?_
  rw [prodLazyK_succ, cLam_sizes.2]
  refine allN_of_forall₀ fun b hb => ?_
  have := h a ha b hb
  unfold c7Run at this
  simp only [strictB_eq₀] at this
  exact this

end CertificateChecks.KernelU6.Sec3
