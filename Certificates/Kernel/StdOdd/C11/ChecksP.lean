module

public import Certificates.Kernel.StdOdd.C11.Data
public import Certificates.Kernel.StdOdd.C11.RK
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

namespace C11

theorem v0 : Nat.beq (nthV D11.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D11.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D11.V) (Nat.add 2 (lenLL D11.prog)) = true := by quickRfl

theorem base : D11.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D11.levOK (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C11.LV CFSG.KD.StdOdd.Cent.C11.levF 10

@[expose] noncomputable def chF (q : ℕ) : Bool := D11.chunkF RO.PL AM BM q

#kc_slices CFSG.KD.StdOdd.Cent.C11.CH CFSG.KD.StdOdd.Cent.C11.chF 16

theorem Lc : D11.LOK AM BM = true := by quickRfl

theorem Hc : D11.HOK AM BM = true := by quickRfl

theorem cand : D11.candF AM BM = true := by quickRfl

@[expose] noncomputable def segC (k : ℕ) : Bool := D11.segF AM BM CK 4 k

#kc_slices CFSG.KD.StdOdd.Cent.C11.SG CFSG.KD.StdOdd.Cent.C11.segC 4

@[expose] noncomputable def RB : ℕ :=
  (List.range 11).foldl (fun a j => a + nthN rs j * nthN nl j) 0

@[expose] noncomputable def orbF (ri : ℕ) : List ℕ := (List.range 11).map fun k => nthN orb (ri * 11 + k)

@[expose] noncomputable def stepF (ri : ℕ) : List (List (List ℕ)) :=
  levSteps (Nat.shiftRight RF (8 * RB * ri)) rs nl (nthN fail ri)

@[expose] noncomputable def rbC (ri : ℕ) : Bool :=
  D11.rbF AM BM (orbF ri) (nthN fail ri) (nthN sidx ri)

#kc_slices CFSG.KD.StdOdd.Cent.C11.RBS CFSG.KD.StdOdd.Cent.C11.rbC 15

@[expose] noncomputable def rcP (q : ℕ) : Bool :=
  flatC 10 4 (fun ri => nthN fail ri)
    (fun ri l k => D11.rchP AM BM RK 4 ri (orbF ri) (stepF ri) l k) q

#kc_slices CFSG.KD.StdOdd.Cent.C11.RCP CFSG.KD.StdOdd.Cent.C11.rcP 600

@[expose] noncomputable def rfC (ri : ℕ) : Bool := D11.rfinF RK 4 ri (orbF ri) (nthN fail ri)

#kc_slices CFSG.KD.StdOdd.Cent.C11.RFS CFSG.KD.StdOdd.Cent.C11.rfC 15

theorem cov : D11.covF (nthN sidx) 15 = true := by quickRfl

theorem RCF : ∀ q < 15 * ((D11.p - 1) * 4), flatC (D11.p - 1) 4 (fun ri => nthN fail ri)
    (fun ri l k => D11.rchF AM BM RK 4 ri (orbF ri) (stepF ri) l k) q = true := fun q hq =>
  @flatC_mono (D11.p - 1) 4 (fun ri => nthN fail ri)
    (fun ri l k => D11.rchP AM BM RK 4 ri (orbF ri) (stepF ri) l k)
    (fun ri l k => D11.rchF AM BM RK 4 ri (orbF ri) (stepF ri) l k)
    (fun a b c h => @rchP_sound D11 AM BM RK 4 a (orbF a) (stepF a) b c h) q (RCP.all q hq)

theorem facts11 : CentFacts D11.p 66 D11.xw D11.d0 D11.e D11.K1 D11.Kall :=
  centFacts_of_start D11 rep_A rep_B bits (Nat.eq_of_beq_eq_true lenOK) v0 v1 P.lines len
    (by decide) (by decide) (by decide) base (fun j hj => LV.all j hj) Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) (fun q hq => CH.all q hq)
    (by decide +kernel) Hc cand (start_of_segs D11 rep_A rep_B (by decide) fun k hk => SG.all k hk)
    (by decide +kernel)
    (refs_of_flat D11 rep_A rep_B v0 v1 P.lines len base (fun j hj => LV.all j hj) (by decide)
      (by decide) (by decide) (RK := RK) (K := 4) (R := 15) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri)
      (fun ri hri => RBS.all ri hri) RCF (fun ri hri => RFS.all ri hri) cov)

end C11

end CFSG.KD.StdOdd.Cent

end
