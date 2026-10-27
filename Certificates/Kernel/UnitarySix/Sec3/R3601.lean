module

public import Certificates.Kernel.UnitarySix.Sec3.E3601Chk
public import Certificates.Kernel.UnitarySix.Sec3.R3600
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum

@[expose] noncomputable def zSL (L : List ℕ) : Bool := strictB (prodL 693 10 (mask 10) L) zSK

@[expose] noncomputable def zSRun (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CA2.LR CA2.TR zSL 2 1
    [CA2.TR (roff 693 (693 * 10) (CA2.LR 0) + (lo + j))]

theorem zS_all (h : ∀ s < 8, zSRun (s * 4) 4 = true) :
    prodLazyK 693 (693 * 10) CA2.LR CA2.TR zSL 3 0 [] = true :=
  loop_of_blocks (N := 8) (B := 4) (by decide +kernel) h

@[expose] noncomputable def a2L (L : List ℕ) : Bool := strictB (prodL 693 10 (mask 10) L) a2K

@[expose] noncomputable def a2Run (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CA2.LR CA2.TR a2L 2 1
    [CA2.TR (roff 693 (693 * 10) (CA2.LR 0) + (lo + j))]

theorem a2_all (h : ∀ s < 4, a2Run (s * 8) 8 = true) :
    prodLazyK 693 (693 * 10) CA2.LR CA2.TR a2L 3 0 [] = true :=
  loop_of_blocks (N := 4) (B := 8) (by decide +kernel) h

@[expose] noncomputable def zA3Run (lo cnt : ℕ) : Bool :=
  strictB (wK we) fun E =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CA3.LR CA3.TR (zA3L E) 1 1
    [CA3.TR (roff 693 (693 * 10) (CA3.LR 0) + (lo + j))]

theorem zA3_all (h : ∀ s < 8, zA3Run (s * 16) 16 = true) :
    prodLazyK 693 (693 * 10) CA3.LR CA3.TR (zA3L (wK we)) 2 0 [] = true :=
  loop_of_blocks (N := 8) (B := 16) (by decide +kernel) fun s hs => by
    have := h s hs
    unfold zA3Run at this
    simp only [strictB_eq₀] at this
    exact this

@[expose] noncomputable def a1L (E : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (a1K E)

@[expose] noncomputable def a1Run (lo cnt : ℕ) : Bool :=
  strictB (wK we) fun E =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CA1.LR CA1.TR (a1L E) 0 1
    [CA1.TR (roff 693 (693 * 10) (CA1.LR 0) + (lo + j))]

theorem a1_all (h : ∀ s < 8, a1Run (s * 64) 64 = true) :
    prodLazyK 693 (693 * 10) CA1.LR CA1.TR (a1L (wK we)) 1 0 [] = true :=
  loop_of_blocks (N := 8) (B := 64) (by decide +kernel) fun s hs => by
    have := h s hs
    unfold a1Run at this
    simp only [strictB_eq₀] at this
    exact this

@[expose] noncomputable def a4L (J JI J2 J2I : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (a4K J JI J2 J2I)

@[expose] noncomputable def a4PairL (L : List ℕ) : Bool :=
  prodLazyK 693 (693 * 10) CX1.LR CX1.TR (fun L' => strictB (prodL 693 10 (mask 10) L') fun Y =>
    strictB (prodL 693 10 (mask 10) L) (a4PairK Y)) 1 0 []

@[expose] noncomputable def a4Run : Bool :=
  strictB (wK wj₀) fun J => strictB (pinvS 693 10 (mask 10) J) fun JI =>
  strictB (wK wj₀sq) fun J2 => strictB (pinvS 693 10 (mask 10) J2) fun J2I =>
  prodLazyK 693 (693 * 10) CA4.LR CA4.TR (a4L J JI J2 J2I) 2 0 [] &&
    prodLazyK 693 (693 * 10) CA4.LR CA4.TR a4PairL 2 0 []

@[expose] noncomputable def z2sL (W WI Gg GgI : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (z2sK W WI Gg GgI)

@[expose] noncomputable def z2sPairL (L : List ℕ) : Bool :=
  prodLazyK 693 (693 * 10) CX1.LR CX1.TR (fun L' => strictB (prodL 693 10 (mask 10) L') fun Y =>
    strictB (prodL 693 10 (mask 10) L) (z2sPairK Y)) 1 0 []

@[expose] noncomputable def z2sRun : Bool :=
  strictB (sec3G 16) fun W => strictB (pinvS 693 10 (mask 10) W) fun WI =>
  strictB (wK wg232) fun Gg => strictB (pinvS 693 10 (mask 10) Gg) fun GgI =>
  prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR (z2sL W WI Gg GgI) 1 0 [] &&
    prodLazyK 693 (693 * 10) CZ2S.LR CZ2S.TR z2sPairL 1 0 []

@[expose] noncomputable def p2Run (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CK1.LR CK1.TR p2L 2 1
    [CK1.TR (roff 693 (693 * 10) (CK1.LR 0) + (lo + j))]

theorem p2_all (h : ∀ s < 30, p2Run (s * 4) 4 = true) :
    prodLazyK 693 (693 * 10) CK1.LR CK1.TR p2L 3 0 [] = true :=
  loop_of_blocks (N := 30) (B := 4) (by decide +kernel) h

end CertificateChecks.KernelU6.Sec3
