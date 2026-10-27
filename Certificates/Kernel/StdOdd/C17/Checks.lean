module

public import Certificates.Kernel.StdOdd.C17.Data
public import Certificates.Kernel.StdOdd.RootOrbit
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

set_option Elab.async false
set_option maxRecDepth 100000

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.Misc.E6Std CFSG.KD.StdOdd.Orbit
  CFSG.Monster.Existence.StdOdd.Cert CFSG.KC.LQT.P

namespace C17

theorem v0 : Nat.beq (nthV D17.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D17.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D17.V) (Nat.add 2 (lenLL D17.prog)) = true := by quickRfl

theorem base : D17.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D17.levOK (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C17.LV CFSG.KD.StdOdd.Cent.C17.levF 16

@[expose] noncomputable def chF (q : ℕ) : Bool := D17.chunkF RO.PL AM BM q

#kc_slices CFSG.KD.StdOdd.Cent.C17.CH CFSG.KD.StdOdd.Cent.C17.chF 16

theorem Lc : D17.LOK AM BM = true := by quickRfl

theorem Hc : D17.HOK AM BM = true := by quickRfl

theorem cand : D17.candF AM BM = true := by quickRfl

theorem start : D17.startF AM BM = true := by quickRfl

theorem noRef : allN 690 (fun r => notB (Nat.beq (nthN D17.st r) 1)) = true := by quickRfl

theorem lenReps : Nat.beq (lenN D17.reps) 690 = true := by quickRfl

theorem facts17 : CentFacts D17.p 17 D17.xw D17.d0 D17.e D17.K1 D17.Kall := by
  refine centFacts_of_checks D17 rep_A rep_B bits (Nat.eq_of_beq_eq_true lenOK) v0 v1 P.lines len
    (by decide) (by decide) (by decide) base (fun j hj => LV.all j hj) Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) (fun q hq => CH.all q hq)
    (by decide +kernel) Hc cand start (by decide +kernel) (fun r hr hs => ?_)
  have h := allN_true noRef r (by rw [← Nat.eq_of_beq_eq_true lenReps]; exact hr)
  rw [hs] at h
  exact absurd h (by decide)

end C17

end CFSG.KD.StdOdd.Cent

end
