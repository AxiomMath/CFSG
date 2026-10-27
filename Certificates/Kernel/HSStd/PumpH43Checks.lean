module

public import Certificates.Kernel.HSStd.PumpH43Data
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.Spor.HNAOrb
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSStd.PumpH43

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HSStd.PumpTC7
open CFSG.KS.HNA (commP)

@[expose] def pairsOf (q : Nat) : List (List Int × List Int) := (derPairs.getD q (#[], [])).2

@[expose] noncomputable def pk (p : Nat) : Bool :=
  permOK 80 7 (mask 7) (80 * 7) p (pinvS 80 7 (mask 7) p)

@[expose] noncomputable def mul (p q : Nat) : Nat := pcomp 80 7 (mask 7) p q

@[expose] noncomputable def one : Nat := pidn 80 7

@[expose] noncomputable def ord3 (p : Nat) : Bool :=
  !Nat.beq p one && Nat.beq (mul p (mul p p)) one

@[expose] noncomputable def inv (CG : Nat → Nat) (k : Nat) : Nat := pinvS 80 7 (mask 7) (CG k)

@[expose] noncomputable def wv (CG : Nat → Nat) (wd : List Int) : Nat :=
  wordK 80 7 (mask 7) (pidn 80 7) CG (inv CG) wd

@[expose] noncomputable def derGensK (CG : Nat → Nat) (pairs : List (List Int × List Int))
    (ng : Nat) (G : Nat → Nat) : Bool :=
  pk (CG 0) && pk (CG 1) && Nat.beq pairs.length ng &&
    allN ng (fun q =>
      wordEqK 80 7 (mask 7) (pidn 80 7) CG (inv CG) 2 ((pairs.getD q ([], [])).1)
        (wv CG (pairs.getD q ([], [])).1) &&
      wordEqK 80 7 (mask 7) (pidn 80 7) CG (inv CG) 2 ((pairs.getD q ([], [])).2)
        (wv CG (pairs.getD q ([], [])).2) &&
      Nat.beq (G q) (commP 80 7 (wv CG (pairs.getD q ([], [])).1) (wv CG (pairs.getD q ([], [])).2)))

theorem sz : szOK 80 7 = true := by quickRfl

theorem gD0 : derGensK CG0 (pairsOf 0) D0.ng D0.G = true := by quickRfl
theorem gD3 : derGensK CG3 (pairsOf 1) D3.ng D3.G = true := by quickRfl
theorem gD9 : derGensK CG9 (pairsOf 2) D9.ng D9.G = true := by quickRfl

theorem permD : (allN D0.ng (fun k => pk (D0.G k)) && allN D3.ng (fun k => pk (D3.G k)) &&
    allN D9.ng (fun k => pk (D9.G k)) && allN 2 (fun k => pk (C10.G k)) &&
    allN 2 (fun k => pk (Q.G k))) = true := by quickRfl

theorem nums : (Nat.beq D0.N 720 && Nat.beq D3.N 720 && Nat.beq D9.N 720 && Nat.beq C10.ng 2 &&
    Nat.beq C10.N 720 && Nat.beq Q.ng 2 && Nat.beq Q.N 74880 && Nat.blt Q.r0 Q.N &&
    Nat.blt (I0 0) C10.N) = true := by quickRfl

theorem kD0 : keysSK 80 7 keys43 D0.N D0.T ((List.range 720).map D0K) = true := by quickRfl
theorem kD3 : keysSK 80 7 keys43 D3.N D3.T ((List.range 720).map D3K) = true := by quickRfl
theorem kD9 : keysSK 80 7 keys43 D9.N D9.T ((List.range 720).map D9K) = true := by quickRfl
theorem kC10 : keysSK 80 7 keys43 C10.N C10.T ((List.range 720).map C10K) = true := by quickRfl

theorem root : (Nat.beq (C10.T (I0 0)) (Q.T Q.r0) && ord3 (C10.T (I0 0)) &&
    allN (I0 0) (fun i => !ord3 (C10.T i))) = true := by quickRfl

theorem wQ : allN C10.N (fun i => !ord3 (C10.T i) ||
    (Nat.blt (QW i) Q.N && Nat.beq (Q.T (QW i)) (C10.T i))) = true := by quickRfl

end CertificateChecks.KernelHSStd.PumpH43

end
