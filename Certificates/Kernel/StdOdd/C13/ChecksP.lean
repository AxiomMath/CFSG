module

public import Certificates.Kernel.StdOdd.C13.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
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

namespace C13

theorem v0 : Nat.beq (nthV D13.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D13.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D13.V) (Nat.add 2 (lenLL D13.prog)) = true := by quickRfl

theorem base : D13.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D13.levOK (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C13.LV CFSG.KD.StdOdd.Cent.C13.levF 12

@[expose] noncomputable def chF (q : ℕ) : Bool := D13.chunkF RO.PL AM BM q

#kc_slices CFSG.KD.StdOdd.Cent.C13.CH CFSG.KD.StdOdd.Cent.C13.chF 16

theorem Lc : D13.LOK AM BM = true := by quickRfl

theorem Hc : D13.HOK AM BM = true := by quickRfl

theorem cand : D13.candF AM BM = true := by quickRfl

@[expose] noncomputable def segC (k : ℕ) : Bool := D13.segF AM BM CK 3 k

#kc_slices CFSG.KD.StdOdd.Cent.C13.SG CFSG.KD.StdOdd.Cent.C13.segC 3

@[expose] noncomputable def RB : ℕ :=
  (List.range 13).foldl (fun a j => a + nthN rs j * nthN nl j) 0

@[expose] noncomputable def orbF (ri : ℕ) : List ℕ :=
  (List.range 13).map fun k => nthN orb (ri * 13 + k)

@[expose] noncomputable def stepF (ri : ℕ) : List (List (List ℕ)) :=
  levSteps (Nat.shiftRight RF (8 * RB * ri)) rs nl (nthN fail ri)

@[expose] noncomputable def rbC (ri : ℕ) : Bool :=
  D13.rbF AM BM (orbF ri) (nthN fail ri) (nthN sidx ri)

#kc_slices CFSG.KD.StdOdd.Cent.C13.RBS CFSG.KD.StdOdd.Cent.C13.rbC 8

@[expose] noncomputable def rcP (q : ℕ) : Bool :=
  flatC 12 3 (fun ri => nthN fail ri)
    (fun ri l k => D13.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k) q

#kc_slices CFSG.KD.StdOdd.Cent.C13.RCP CFSG.KD.StdOdd.Cent.C13.rcP 288

@[expose] noncomputable def rfC (ri : ℕ) : Bool := D13.rfinF RK 3 ri (orbF ri) (nthN fail ri)

#kc_slices CFSG.KD.StdOdd.Cent.C13.RFS CFSG.KD.StdOdd.Cent.C13.rfC 8

theorem cov : D13.covF (nthN sidx) 8 = true := by quickRfl

theorem RCF : ∀ q < 8 * ((D13.p - 1) * 3), flatC (D13.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D13.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k) q = true := fun q hq =>
  @flatC_mono (D13.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D13.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun ri l k => D13.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun a b c h => @rchP_sound D13 AM BM RK 3 a (orbF a) (stepF a) b c h) q (RCP.all q hq)

theorem facts13 : CentFacts D13.p 13 D13.xw D13.d0 D13.e D13.K1 D13.Kall :=
  centFacts_of_start D13 rep_A rep_B bits (Nat.eq_of_beq_eq_true lenOK) v0 v1 P.lines len
    (by decide) (by decide) (by decide) base (fun j hj => LV.all j hj) Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) (fun q hq => CH.all q hq)
    (by decide +kernel) Hc cand
    (start_of_segs D13 rep_A rep_B (by decide) fun k hk => SG.all k hk)
    (by decide +kernel)
    (refs_of_flat D13 rep_A rep_B v0 v1 P.lines len base (fun j hj => LV.all j hj) (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 8) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C13

end CFSG.KD.StdOdd.Cent

end
