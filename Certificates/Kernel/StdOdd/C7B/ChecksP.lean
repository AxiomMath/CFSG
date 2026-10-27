module

public import Certificates.Kernel.StdOdd.C7B.Data
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

namespace C7B

theorem v0 : Nat.beq (nthV D7B.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D7B.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D7B.V) (Nat.add 2 (lenLL D7B.prog)) = true := by quickRfl

theorem base : D7B.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D7B.levOK (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C7B.LV CFSG.KD.StdOdd.Cent.C7B.levF 6

@[expose] noncomputable def chF (q : ℕ) : Bool := D7B.chunkF RO.PL AM BM q

#kc_slices CFSG.KD.StdOdd.Cent.C7B.CH CFSG.KD.StdOdd.Cent.C7B.chF 16

theorem Lc : D7B.LOK AM BM = true := by quickRfl

theorem Hc : D7B.HOK AM BM = true := by quickRfl

theorem candI : D7B.candIni AM BM = true := by quickRfl

@[expose] noncomputable def csegC (k : ℕ) : Bool := D7B.csegF AM BM CC 6 3 k

#kc_slices CFSG.KD.StdOdd.Cent.C7B.CS CFSG.KD.StdOdd.Cent.C7B.csegC 3

@[expose] noncomputable def segC (k : ℕ) : Bool := D7B.segF AM BM CK 3 k

#kc_slices CFSG.KD.StdOdd.Cent.C7B.SG CFSG.KD.StdOdd.Cent.C7B.segC 3

@[expose] noncomputable def RB : ℕ :=
  (List.range 7).foldl (fun a j => a + nthN rs j * nthN nl j) 0

@[expose] noncomputable def orbF (ri : ℕ) : List ℕ :=
  (List.range 7).map fun k => nthN orb (ri * 7 + k)

@[expose] noncomputable def stepF (ri : ℕ) : List (List (List ℕ)) :=
  levSteps (Nat.shiftRight RF (8 * RB * ri)) rs nl (nthN fail ri)

@[expose] noncomputable def rbC (ri : ℕ) : Bool :=
  D7B.rbF AM BM (orbF ri) (nthN fail ri) (nthN sidx ri)

#kc_slices CFSG.KD.StdOdd.Cent.C7B.RBS CFSG.KD.StdOdd.Cent.C7B.rbC 29

@[expose] noncomputable def rcP (q : ℕ) : Bool :=
  flatC 6 3 (fun ri => nthN fail ri)
    (fun ri l k => D7B.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k) q

#kc_slices CFSG.KD.StdOdd.Cent.C7B.RCP CFSG.KD.StdOdd.Cent.C7B.rcP 522

@[expose] noncomputable def rfC (ri : ℕ) : Bool := D7B.rfinF RK 3 ri (orbF ri) (nthN fail ri)

#kc_slices CFSG.KD.StdOdd.Cent.C7B.RFS CFSG.KD.StdOdd.Cent.C7B.rfC 29

theorem cov : D7B.covF (nthN sidx) 29 = true := by quickRfl

theorem RCF : ∀ q < 29 * ((D7B.p - 1) * 3), flatC (D7B.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D7B.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k) q = true := fun q hq =>
  @flatC_mono (D7B.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D7B.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun ri l k => D7B.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun a b c h => @rchP_sound D7B AM BM RK 3 a (orbF a) (stepF a) b c h) q (RCP.all q hq)

theorem facts7B : CentFacts D7B.p 1176 D7B.xw D7B.d0 D7B.e D7B.K1 D7B.Kall :=
  centFacts_of_walks D7B rep_A rep_B bits (Nat.eq_of_beq_eq_true lenOK) v0 v1 P.lines len
    (by decide) (by decide) (by decide) base (fun j hj => LV.all j hj) Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) (fun q hq => CH.all q hq)
    (by decide +kernel) Hc candI (cand_of_csegs D7B (by decide) fun k hk => CS.all k hk)
    (start_of_segs D7B rep_A rep_B (by decide) fun k hk => SG.all k hk)
    (by decide +kernel)
    (refs_of_flat D7B rep_A rep_B v0 v1 P.lines len base (fun j hj => LV.all j hj) (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 29) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C7B

end CFSG.KD.StdOdd.Cent

end
