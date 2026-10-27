module

public import Certificates.Kernel.UnitarySix.Sec3.R3600
public import Certificates.Kernel.UnitarySix.Sec3.E3601Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3YElt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

@[expose] noncomputable def memL (k : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => Nat.beq h k || ih) L

@[expose] noncomputable def isId (X : ℕ) : Bool := Nat.beq X (pidn 693 10)

@[expose] noncomputable def key3L (L : List ℕ) : ℕ :=
  Nat.add (ptL 10 (mask 10) L 45)
    (Nat.mul 1024 (Nat.add (ptL 10 (mask 10) L 3) (Nat.mul 1024 (ptL 10 (mask 10) L 1))))

@[expose] noncomputable def a2OrbL (L : List ℕ) : Bool :=
  (ptL 10 (mask 10) L 45 != 45 || ptL 10 (mask 10) L 3 != 3 || ptL 10 (mask 10) L 1 != 1 ||
    strictB (prodL 693 10 (mask 10) L) isId) &&
  (memL (key3L L) a2Keys || strictB (prodL 693 10 (mask 10) L) isId)

@[expose] noncomputable def a1OrbL (L : List ℕ) : Bool :=
  (ptL 10 (mask 10) L 1 != 1 || strictB (prodL 693 10 (mask 10) L) isId) &&
  (memL (ptL 10 (mask 10) L 1) a1Keys || memL (ptL 10 (mask 10) L 1) a1KeysZ ||
    ptL 10 (mask 10) L 1 == 1 || ptL 10 (mask 10) L 1 == pg 10 (mask 10) (sec3G 14) 1)

@[expose] noncomputable def keyA3L (L : List ℕ) : ℕ :=
  Nat.add (Nat.mul (ptL 10 (mask 10) L 205) 1024) (ptL 10 (mask 10) L 251)

@[expose] noncomputable def a3OrbL (L : List ℕ) : Bool :=
  (ptL 10 (mask 10) L 205 != 205 || ptL 10 (mask 10) L 251 != 251 ||
    strictB (prodL 693 10 (mask 10) L) sfA4) &&
  (memL (keyA3L L) a3Keys || keyA3L L == 205 * 1024 + 251)

@[expose] noncomputable def singL (L : List ℕ) : Bool :=
  ptL 10 (mask 10) L (ptL 10 (mask 10) L 1) != 1 || memL (ptL 10 (mask 10) L 1) singKeys ||
    memL (ptL 10 (mask 10) L 1) singKeysZ

@[expose] noncomputable def a2OrbRun : Bool :=
  prodLazyK 693 (693 * 10) CA2.LR CA2.TR a2OrbL 3 0 []

@[expose] noncomputable def a1OrbRun : Bool :=
  prodLazyK 693 (693 * 10) CA1.LR CA1.TR a1OrbL 1 0 [] &&
    prodLazyK 693 (693 * 10) CA1.LR CA1.TR singL 1 0 []

@[expose] noncomputable def a3OrbRun (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CA3.LR CA3.TR a3OrbL 1 1
    [CA3.TR (roff 693 (693 * 10) (CA3.LR 0) + (lo + j))]

theorem a3Orb_all (h : ∀ s < 4, a3OrbRun (s * 32) 32 = true) :
    prodLazyK 693 (693 * 10) CA3.LR CA3.TR a3OrbL 2 0 [] = true :=
  loop_of_blocks (N := 4) (B := 32) (by decide +kernel) h

end CertificateChecks.KernelU6.Sec3
