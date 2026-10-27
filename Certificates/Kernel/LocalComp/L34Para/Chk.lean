module

public import Certificates.Kernel.LocalComp.L34Para.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Para

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

theorem kT_gens : gensK (wordTabs wT₀) 42 6 4 L34PT.G = true := by quickRfl
theorem kT_hd : penumHdK (pidn 42 6) 64 64 L34PT.T L34PT.PL = true := by quickRfl
theorem kT_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34PT.G L34PT.GI 4 64 L34PT.T L34PT.PL
    L34PT.POS L34PT.SRT L34PT.SRI 0 64 = true := by
  quickRfl

theorem kB_gens : gensK (wordTabs wB₀) 42 6 3 L34PB.G = true := by quickRfl
theorem kB_hd : penumHdK (pidn 42 6) 192 192 L34PB.T L34PB.PL = true := by quickRfl
theorem kB_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34PB.G L34PB.GI 3 192 L34PB.T L34PB.PL
    L34PB.POS L34PB.SRT L34PB.SRI 0 192 = true := by
  quickRfl

theorem kP1_gens : gensK (wordTabs wP₁) 42 6 3 L34P1.G = true := by quickRfl
theorem kP1_hd : penumHdK (pidn 42 6) 960 960 L34P1.T L34P1.PL = true := by quickRfl
theorem kP1_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34P1.G L34P1.GI 3 960 L34P1.T L34P1.PL
    L34P1.POS L34P1.SRT L34P1.SRI 0 960 = true := by
  quickRfl

theorem kP2_gens : gensK (wordTabs wP₂) 42 6 3 L34P2.G = true := by quickRfl
theorem kP2_hd : penumHdK (pidn 42 6) 960 960 L34P2.T L34P2.PL = true := by quickRfl
theorem kP2_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34P2.G L34P2.GI 3 960 L34P2.T L34P2.PL
    L34P2.POS L34P2.SRT L34P2.SRI 0 960 = true := by
  quickRfl

theorem kY : gensK (wordTabs wReps) 42 6 105 L34PR.Y = true := by quickRfl

@[expose] noncomputable def bInv (j : Nat) : Nat := pinvS 42 6 (mask 6) (L34PB.G j)

theorem kYI : allN 105 (fun k => andB (canonK 42 6 (mask 6) (42 * 6) (L34PR.YI k))
    (Nat.beq (pcomp 42 6 (mask 6) (L34PR.Y k) (L34PR.YI k)) (pidn 42 6))) = true := by
  quickRfl

theorem kBI : allN 3 (fun j => andB (canonK 42 6 (mask 6) (42 * 6) (bInv j))
    (Nat.beq (pcomp 42 6 (mask 6) (L34PB.G j) (bInv j)) (pidn 42 6))) = true := by
  quickRfl

@[expose] noncomputable def memK (N : Nat) (T : Nat → Nat) (x : Nat) : Bool :=
  notB (allN N fun q => notB (Nat.beq (T q) x))

theorem kNorm : allN 3 (fun j => allN 4 fun i =>
    andB (memK 64 L34PT.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34PB.G j) (L34PT.G i))
      (bInv j)))
      (memK 64 L34PT.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (bInv j) (L34PT.G i))
        (L34PB.G j)))) = true := by
  quickRfl

theorem kInP : allN 3 (fun j => andB (memK 960 L34P1.T (L34PB.G j)) (memK 960 L34P2.T (L34PB.G j))) =
    true := by
  quickRfl

theorem kCos : allN 20160 (fun i => strictB (L34PC.C i) fun c =>
    strictB (Nat.land c 255) fun k => strictB (Nat.shiftRight c 8) fun q =>
      andB (Nat.blt k 105) (andB (Nat.blt q 192)
        (Nat.beq (L34PB.T q) (pcomp 42 6 (mask 6) (L34PR.YI k) (L34S.T i))))) = true := by
  quickRfl

@[expose] noncomputable def listed (k : Nat) : Bool :=
  notB (allN 96 fun e => notB (Nat.beq (L34PW.WL.getD (Nat.mul 4 e) 0) k))

theorem kReps : allN 105 (fun k => orB (memK 960 L34P1.T (L34PR.Y k))
    (orB (memK 960 L34P2.T (L34PR.Y k)) (listed k))) = true := by
  quickRfl

theorem kWords : allN 96 (fun e => strictB (L34PW.WL.getD (Nat.mul 4 e) 0) fun k =>
    andB (Nat.blt k 105) (allN 3 fun i => Nat.beq (CFSG.KC.L34Two.dwordK 42 6 (L34PW.A k) 4 16
      (L34PW.WL.getD (Nat.add (Nat.add (Nat.mul 4 e) 1) i) 0)) (L34R.G i))) = true := by
  quickRfl

theorem kNeg : andB (notB (memK 959 (fun q => L34P1.T (Nat.succ q)) (pidn 42 6)))
    (notB (Nat.beq (CFSG.KC.L34Two.dwordK 42 6 (L34PW.A (L34PW.WL.getD 0 0)) 4 16
      (L34PW.WL.getD 2 0)) (L34R.G 0))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Para

end
