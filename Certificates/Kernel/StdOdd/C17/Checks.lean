module

public import Certificates.Kernel.StdOdd.C17.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
public import Certificates.Kernel.StdOdd.RootOrbit
public import Certificates.Kernel.StdOdd.C17.ChecksX
public import Certificates.Kernel.StdOdd.CentOrbGlue
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

set_option Elab.async false
set_option maxRecDepth 100000

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.Misc.E6Std CFSG.KD.StdOdd.Orbit
  CFSG.Monster.Existence.StdOdd.Cert CFSG.KC.LQT.P CFSG.KS.StdOdd.Chain Matrix

namespace C17

theorem v0 : Nat.beq (nthV D17.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D17.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D17.V) (Nat.add 2 (lenLL D17.prog)) = true := by quickRfl

theorem base : D17.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D17.levQ 8640 (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C17.LV CFSG.KD.StdOdd.Cent.C17.levF 16

theorem LVK : ∀ j < D17.p - 1, D17.LevFact (j + 1) := fun j hj =>
  levFact_of_levOK D17 (levQ_sound D17 (LV.all j hj))

theorem nbAll : ∀ c < 156, Nat.beq (net RO.DS NX (nthN RO.PL c))
    (orbPlane (D17.xB AM BM) UR 233415 17 c) = true := fun c hc => by
  have hs : c / 12 < 13 := by omega
  have h0 : orbNetOK RO.DS NX RO.PL (D17.xB AM BM) UR 233415 17 12 (c / 12) = true :=
    NBX.all (c / 12) hs
  have h := orbNetOK_sound h0 (c % 12) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem cntK1 : ((Finset.range 3968055).filter fun i => ∀ k ∈ D17.K1,
    rhoC (ptK RO.PL i) (wM D17.xw ^ k.1 *ᵥ ptK RO.PL i) = k.2).card = D17.s := by
  have e : (17 * 233415 + 0 : ℕ) = 3968055 := rfl
  have hf : Nat.beq (net RO.DS NX (full (17 * 233415 + 0))) (full (17 * 233415 + 0)) = true := by
    rw [e]
    exact nxFull
  have h := D17.card_prof_orb (PL := RO.PL) (Ds := RO.DS) (Ms := NX) (U := UR) (cs := cr)
    (m := 233415) (p := 17) (f := 0) (Q := 1) (d := 18) (rep_wM rep_A rep_B D17.xw) (by decide)
    (by norm_num) (lenN_leafPl _ _ _) nxOK hf nbAll (by norm_num) (fun q hq => CRX.all q hq)
    orbFix
  have e2 : 17 * ∑ q ∈ Finset.range 1, nthN cr q = D17.s := by decide +kernel
  rw [e, e2] at h
  exact h

theorem Lc : D17.LOK AM BM = true := by quickRfl

theorem Hc : D17.HOK AM BM = true := by quickRfl

theorem cand : D17.candF AM BM = true := by quickRfl

theorem start : D17.startP AM BM = true := by quickRfl

theorem noRef : allN 690 (fun r => notB (Nat.beq (nthN D17.st r) 1)) = true := by quickRfl

theorem lenReps : Nat.beq (lenN D17.reps) 690 = true := by quickRfl

theorem facts17 : CentFacts D17.p 17 D17.xw D17.d0 D17.e D17.K1 D17.Kall := by
  refine centFacts_of_count D17 rep_A rep_B bits v0 v1 P.lines len
    (by decide) (by decide) (by decide) base LVK Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) cntK1 Hc
    (candWalk_of_candF D17 cand).1 (candWalk_of_candF D17 cand).2
    (start_of_startF D17 rep_A rep_B (startP_sound D17 start)) (by decide +kernel)
    (fun r hr hs => ?_)
  have h := allN_true noRef r (by rw [← Nat.eq_of_beq_eq_true lenReps]; exact hr)
  rw [hs] at h
  exact absurd h (by decide)

end C17

end CFSG.KD.StdOdd.Cent

end
