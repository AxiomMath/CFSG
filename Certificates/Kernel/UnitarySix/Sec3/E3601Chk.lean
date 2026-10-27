module

public import Certificates.Kernel.UnitarySix.Sec3.G3601Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XElt
public import Certificates.Data.Kernel.U6.Sec3LabA3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

@[expose] noncomputable def sfZ (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CZ.LR CZ.TRI CZ.BP 1 0 G
@[expose] noncomputable def sfX1Z (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX1Z.LR CX1Z.TRI CX1Z.BP 1 0 G
@[expose] noncomputable def sfX6Z (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX6Z.LR CX6Z.TRI CX6Z.BP 1 0 G
@[expose] noncomputable def sfX8 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX8.LR CX8.TRI CX8.BP 1 0 G
@[expose] noncomputable def sfZ2S (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CZ2S.LR CZ2S.TRI CZ2S.BP 1 0 G
@[expose] noncomputable def sfP2 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CP2.LR CP2.TRI CP2.BP 3 0 G

@[expose] noncomputable def commK (X Y : ℕ) : Bool :=
  Nat.beq (pcomp 693 10 (mask 10) X Y) (pcomp 693 10 (mask 10) Y X)

@[expose] noncomputable def commFailK (L : List ℕ) (Y : ℕ) : Bool :=
  commPts.any fun p => ptL 10 (mask 10) L (pg 10 (mask 10) Y p) != pg 10 (mask 10) Y
    (ptL 10 (mask 10) L p)

theorem chX6Z_P : ∀ j < chX6Z.gens.length, PermK (CX6Z.S j) (CX6Z.SI j) = true := by
  decide +kernel
theorem chX1_P : ∀ j < chX1.gens.length, PermK (CX1.S j) (CX1.SI j) = true := by decide +kernel

@[expose] noncomputable def zSK (X : ℕ) : Bool :=
  !((List.range chS.gens.length).all fun j => commK X (CS.S j)) || sfZ X

@[expose] noncomputable def zA3L (E : ℕ) (L : List ℕ) : Bool :=
  ((List.range chA3.gens.length).any (fun j => commFailK L (CA3.S j)) ||
    strictB (prodL 693 10 (mask 10) L) fun X =>
      !((List.range chA3.gens.length).all fun j => commK X (CA3.S j)) || sfA4 X) &&
  (commFailK L E || strictB (prodL 693 10 (mask 10) L) fun X => !(commK X E) || sfA4 X)

@[expose] noncomputable def a1K (E X : ℕ) : Bool :=
  (!((List.range chA1.gens.length).all fun j => commK X (CA1.S j)) || sfZ X) &&
  (!(commK X E) || sfX1Z X) &&
  (!((List.range chX6Z.gens.length).all fun j => commK X (CX6Z.S j)) || sfA2 X)

@[expose] noncomputable def a2K (X : ℕ) : Bool := !(sfA1 X) || sfX6Z X

@[expose] noncomputable def a4K (J JI J2 J2I X : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) X) fun xi => PermK X xi &&
  ((!((List.range chX1.gens.length).all fun j => commK X (CX1.S j)) || sfZ X) &&
  (!(sfA1 X) || sfZ2S X) &&
  sfX8 (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) X J) (pcomp 693 10 (mask 10) xi JI)) &&
  sfX8 (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) X J2) (pcomp 693 10 (mask 10) xi J2I)))

@[expose] noncomputable def a4PairK (Y X : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) Y) fun yi => strictB (pinvS 693 10 (mask 10) X) fun xi =>
  PermK Y yi && PermK X xi && (Nat.beq Y (pidn 693 10) ||
    !(sfZ (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) Y X) (pcomp 693 10 (mask 10) yi xi))) ||
    sfZ2S X)

@[expose] noncomputable def z2sK (W WI Gg GgI X : ℕ) : Bool :=
  (!(sfZ2S (pcomp 693 10 (mask 10) W (pcomp 693 10 (mask 10) X WI))) || sfZ X) &&
  (!(sfZ2S (pcomp 693 10 (mask 10) Gg (pcomp 693 10 (mask 10) X GgI))) || sfZ X)

@[expose] noncomputable def z2sPairK (Y X : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) Y) fun yi => strictB (pinvS 693 10 (mask 10) X) fun xi =>
  PermK Y yi && PermK X xi &&
    sfZ (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) Y X) (pcomp 693 10 (mask 10) yi xi))

@[expose] noncomputable def p2K (X : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) X) fun xi => PermK X xi &&
    (!((List.range chA3.gens.length).all fun j =>
      sfA3 (pcomp 693 10 (mask 10) X (pcomp 693 10 (mask 10) (CA3.S j) xi))) || sfP2 X)

@[expose] noncomputable def p2L (L : List ℕ) : Bool :=
  !((List.range chA3.gens.length).all fun j => pg 10 (mask 10) sec3LabA3
      (ptL 10 (mask 10) L (pg 10 (mask 10) (CA3.S j) 2)) == pg 10 (mask 10) sec3LabA3
      (ptL 10 (mask 10) L 2)) ||
    p2K (prodL 693 10 (mask 10) L)

abbrev we : List ℕ := [4, 17]
abbrev wj₀sq : List ℕ := [15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1]
abbrev wg232 : List ℕ := [16, 17, 16]

theorem perm_we : PermK (wK we) (wKI we) = true := perm_words2 _ (by simp)
theorem perm_wj₀sq : PermK (wK wj₀sq) (wKI wj₀sq) = true := perm_words2 _ (by simp)
theorem perm_wg232 : PermK (wK wg232) (wKI wg232) = true := perm_words2 _ (by simp)
theorem perm_wj₀ : PermK (wK wj₀) (wKI wj₀) = true := perm_words _ (by simp)

theorem labA3_eq : ∀ x < 693, labA3[x]! = pg 10 (mask 10) sec3LabA3 x := by decide +kernel

end CertificateChecks.KernelU6.Sec3
