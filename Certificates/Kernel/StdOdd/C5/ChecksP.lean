module

public import Certificates.Kernel.StdOdd.C5.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
public import Certificates.Kernel.StdOdd.CentPopH
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

namespace C5

theorem v0 : Nat.beq (nthV D5.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D5.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D5.V) (Nat.add 2 (lenLL D5.prog)) = true := by quickRfl

theorem base : D5.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D5.levOK (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C5.LV CFSG.KD.StdOdd.Cent.C5.levF 4

@[expose] noncomputable def chF (q : ℕ) : Bool := D5.chunkH 18 RO.PL AM BM q

#kc_slices CFSG.KD.StdOdd.Cent.C5.CH CFSG.KD.StdOdd.Cent.C5.chF 16

theorem Lc : D5.LOK AM BM = true := by quickRfl

theorem Hc : D5.HOK AM BM = true := by quickRfl

theorem candI : D5.candIni AM BM = true := by quickRfl

@[expose] noncomputable def csegC (k : ℕ) : Bool := D5.csegH AM BM CC 3 3 k 17

#kc_slices CFSG.KD.StdOdd.Cent.C5.CS CFSG.KD.StdOdd.Cent.C5.csegC 3

@[expose] noncomputable def segC (k : ℕ) : Bool := D5.segF AM BM CK 3 k

#kc_slices CFSG.KD.StdOdd.Cent.C5.SG CFSG.KD.StdOdd.Cent.C5.segC 3

@[expose] noncomputable def RB : ℕ :=
  (List.range 5).foldl (fun a j => a + nthN rs j * nthN nl j) 0

@[expose] noncomputable def orbF (ri : ℕ) : List ℕ :=
  (List.range 5).map fun k => nthN orb (ri * 5 + k)

@[expose] noncomputable def stepF (ri : ℕ) : List (List (List ℕ)) :=
  levSteps (Nat.shiftRight RF (8 * RB * ri)) rs nl (nthN fail ri)

@[expose] noncomputable def rbC (ri : ℕ) : Bool :=
  D5.rbF AM BM (orbF ri) (nthN fail ri) (nthN sidx ri)

#kc_slices CFSG.KD.StdOdd.Cent.C5.RBS CFSG.KD.StdOdd.Cent.C5.rbC 7

@[expose] noncomputable def rcP (q : ℕ) : Bool :=
  flatC 4 3 (fun ri => nthN fail ri)
    (fun ri l k => D5.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k) q

#kc_slices CFSG.KD.StdOdd.Cent.C5.RCP CFSG.KD.StdOdd.Cent.C5.rcP 84

@[expose] noncomputable def rfC (ri : ℕ) : Bool := D5.rfinF RK 3 ri (orbF ri) (nthN fail ri)

#kc_slices CFSG.KD.StdOdd.Cent.C5.RFS CFSG.KD.StdOdd.Cent.C5.rfC 7

theorem cov : D5.covF (nthN sidx) 7 = true := by quickRfl

theorem RCF : ∀ q < 7 * ((D5.p - 1) * 3), flatC (D5.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D5.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k) q = true := fun q hq =>
  @flatC_mono (D5.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D5.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun ri l k => D5.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun a b c h => @rchP_sound D5 AM BM RK 3 a (orbF a) (stepF a) b c h) q (RCP.all q hq)

theorem facts5 : CentFacts D5.p 100800 D5.xw D5.d0 D5.e D5.K1 D5.Kall :=
  centFacts_of_walks D5 rep_A rep_B bits (Nat.eq_of_beq_eq_true lenOK) v0 v1 P.lines len
    (by decide) (by decide) (by decide) base (fun j hj => LV.all j hj) Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide)
    (fun q hq => D5.chunkF_of_chunkH (CH.all q hq)) (by decide +kernel) Hc candI
    (cand_of_csegs D5 (by decide) fun k hk => D5.csegF_of_csegH (CS.all k hk))
    (start_of_segs D5 rep_A rep_B (by decide) fun k hk => SG.all k hk)
    (by decide +kernel)
    (refs_of_flat D5 rep_A rep_B v0 v1 P.lines len base (fun j hj => LV.all j hj) (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 7) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C5

end CFSG.KD.StdOdd.Cent

end
