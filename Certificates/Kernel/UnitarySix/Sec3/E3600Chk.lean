module

public import Certificates.Kernel.UnitarySix.Sec3.GensChk
public import Certificates.Kernel.UnitarySix.Sec3.CS
public import Certificates.Kernel.UnitarySix.Sec3.CX1
public import Certificates.Kernel.UnitarySix.Sec3.CX2
public import Certificates.Kernel.UnitarySix.Sec3.CX3
public import Certificates.Kernel.UnitarySix.Sec3.CK1
public import Certificates.Kernel.UnitarySix.Sec3.CK2
public import Certificates.Kernel.UnitarySix.Sec3.CA1
public import Certificates.Kernel.UnitarySix.Sec3.CA2
public import Certificates.Kernel.UnitarySix.Sec3.CK1A1
public import Certificates.Kernel.UnitarySix.Sec3.CK2A2
public import Certificates.Kernel.UnitarySix.Sec3.CL
public import Certificates.Kernel.UnitarySix.Sec3.CB12
public import Certificates.Kernel.UnitarySix.Sec3.CB23
public import Certificates.Kernel.UnitarySix.Sec3.CSJ
public import Certificates.Kernel.UnitarySix.Sec3.CT1
public import Certificates.Kernel.UnitarySix.Sec3.CT2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Elt
public import Certificates.Data.Kernel.U6.Sec3Lab
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.U6Sec3Defs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

@[expose] noncomputable def wK (w : List ℕ) : ℕ := wordGA sec3G w

@[expose] noncomputable def wKI (w : List ℕ) : ℕ := pinvS 693 10 (mask 10) (wK w)

abbrev wu₁ : List ℕ := [15, 16, 17, 16, 15]
abbrev wu₂ : List ℕ := [17, 16, 17, 15, 16, 17]
abbrev ww₀ : List ℕ := [15, 16, 17, 15, 16, 17, 15, 16, 17]
abbrev wj₀ : List ℕ := [15, 1, 15, 0, 1, 15, 1]
abbrev wab : List ℕ := [15, 16]
abbrev wba : List ℕ := [16, 15]
abbrev waba : List ℕ := [15, 16, 15]
abbrev wbcb : List ℕ := [16, 17, 16]

theorem perm_words : ∀ w ∈ [wu₁, wu₂, ww₀, wj₀, wab, wba, waba, wbcb], PermK (wK w) (wKI w) = true := by
  decide +kernel

@[expose] noncomputable def sfS (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CS.LR CS.TRI CS.BP 3 0 G
@[expose] noncomputable def sfX1 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX1.LR CX1.TRI CX1.BP 1 0 G
@[expose] noncomputable def sfX2 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX2.LR CX2.TRI CX2.BP 1 0 G
@[expose] noncomputable def sfX3 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CX3.LR CX3.TRI CX3.BP 1 0 G
@[expose] noncomputable def sfK1 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CK1.LR CK1.TRI CK1.BP 3 0 G
@[expose] noncomputable def sfK2 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CK2.LR CK2.TRI CK2.BP 3 0 G
@[expose] noncomputable def sfK1A1 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CK1A1.LR CK1A1.TRI CK1A1.BP 4 0 G
@[expose] noncomputable def sfK2A2 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CK2A2.LR CK2A2.TRI CK2A2.BP 3 0 G
@[expose] noncomputable def sfSJ (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CSJ.LR CSJ.TRI CSJ.BP 3 0 G
@[expose] noncomputable def sfT1 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CT1.LR CT1.TRI CT1.BP 2 0 G
@[expose] noncomputable def sfT2 (G : ℕ) : Bool :=
  siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) CT2.LR CT2.TRI CT2.BP 2 0 G

@[expose] noncomputable def sIntK2 (u2 u2i X : ℕ) : Bool :=
  sfS (pcomp 693 10 (mask 10) u2 (pcomp 693 10 (mask 10) X u2i)) == sfT2 X

@[expose] noncomputable def sIntK1 (u1 u1i w0 w0i X : ℕ) : Bool :=
  (sfS (pcomp 693 10 (mask 10) u1 (pcomp 693 10 (mask 10) X u1i)) == sfT1 X) &&
  (Nat.beq X (pidn 693 10) || !(sfS (pcomp 693 10 (mask 10) w0 (pcomp 693 10 (mask 10) X w0i))))

@[expose] noncomputable def sIntL (u2 u2i u1 u1i w0 w0i : ℕ) (L : List ℕ) : Bool :=
  (ptL 10 (mask 10) L 381 != 381 || strictB (prodL 693 10 (mask 10) L) (sIntK2 u2 u2i)) &&
  (ptL 10 (mask 10) L 1 != 1 || strictB (prodL 693 10 (mask 10) L) (sIntK1 u1 u1i w0 w0i))

@[expose] noncomputable def t2IntK (p pi q qi r ri X : ℕ) : Bool :=
  (sfT2 (pcomp 693 10 (mask 10) p (pcomp 693 10 (mask 10) X pi)) == sfX1 X) &&
  (sfT2 (pcomp 693 10 (mask 10) q (pcomp 693 10 (mask 10) X qi)) == sfX2 X) &&
  (Nat.beq X (pidn 693 10) || !(sfT2 (pcomp 693 10 (mask 10) r (pcomp 693 10 (mask 10) X ri))))

@[expose] noncomputable def t1IntK (p pi X : ℕ) : Bool :=
  sfT1 (pcomp 693 10 (mask 10) p (pcomp 693 10 (mask 10) X pi)) == sfX3 X

@[expose] noncomputable def ka1K (X : ℕ) : Bool :=
  Nat.beq X (pidn 693 10) || (pg 10 (mask 10) X 1 != 1 && !(sfK1 X))

@[expose] noncomputable def ka2K (u2 u2i X : ℕ) : Bool :=
  Nat.beq X (pidn 693 10) || (!(sfK2 X) &&
    !(sfK2A2 (pcomp 693 10 (mask 10) u2 (pcomp 693 10 (mask 10) X u2i))))

@[expose] noncomputable def normK (X : ℕ) : Bool :=
  strictB (pinvS 693 10 (mask 10) X) fun xi => PermK X xi &&
    (!((List.range 5).all fun j =>
      sfS (pcomp 693 10 (mask 10) X (pcomp 693 10 (mask 10) (CS.S j) xi))) || sfSJ X)

@[expose] noncomputable def normL (L : List ℕ) : Bool :=
  !((List.range 6).all fun j => pg 10 (mask 10) sec3LabT1
      (ptL 10 (mask 10) L (pg 10 (mask 10) (CT1.S j) 9)) == pg 10 (mask 10) sec3LabT1
      (ptL 10 (mask 10) L 9)) ||
    normK (prodL 693 10 (mask 10) L)

theorem chS_P : ∀ j < 5, PermK (CS.S j) (CS.SI j) = true := by decide +kernel

theorem labT1_eq : ∀ x < 693, labT1[x]! = pg 10 (mask 10) sec3LabT1 x := by decide +kernel

theorem chT1_P : ∀ j < 6, PermK (CT1.S j) (CT1.SI j) = true := by decide +kernel

end CertificateChecks.KernelU6.Sec3
