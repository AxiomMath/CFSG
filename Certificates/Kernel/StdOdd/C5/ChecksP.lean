module

public import Certificates.Kernel.StdOdd.C5.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
public import Certificates.Kernel.StdOdd.CentPopH
public import Certificates.Kernel.StdOdd.RootOrbit
public import Certificates.Kernel.StdOdd.C5.ChecksX
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

namespace C5

theorem v0 : Nat.beq (nthV D5.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D5.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D5.V) (Nat.add 2 (lenLL D5.prog)) = true := by quickRfl

theorem base : D5.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D5.levQZ 8640 (j + 3)

#kc_slices CFSG.KD.StdOdd.Cent.C5.LV CFSG.KD.StdOdd.Cent.C5.levF 2

theorem LI1 : D5.levIni 1 = true := by quickRfl

theorem LI2 : D5.levIni 2 = true := by quickRfl

@[expose] noncomputable def lsegC1 (k : ℕ) : Bool := D5.lsegZ 1 LC1 4 7 k

#kc_slices CFSG.KD.StdOdd.Cent.C5.LS1 CFSG.KD.StdOdd.Cent.C5.lsegC1 7

@[expose] noncomputable def lsegC2 (k : ℕ) : Bool := D5.lsegZ 2 LC2 4 7 k

#kc_slices CFSG.KD.StdOdd.Cent.C5.LS2 CFSG.KD.StdOdd.Cent.C5.lsegC2 7

theorem LVK : ∀ j < D5.p - 1, D5.LevFact (j + 1)
  | 0, _ => levFact_of_segs D5 (cc := LC1) (g := 4) LI1 (by decide) fun k hk =>
      D5.lsegF_of_lsegZ (LS1.all k hk)
  | 1, _ => levFact_of_segs D5 (cc := LC2) (g := 4) LI2 (by decide) fun k hk =>
      D5.lsegF_of_lsegZ (LS2.all k hk)
  | j + 2, hj => levFact_of_levOK D5 (levQZ_sound D5 (LV.all j (by
      have : D5.p = 5 := rfl
      change j < 2
      omega)))

theorem nbAll : ∀ c < 156, Nat.beq (net RO.DS NX (nthN RO.PL c))
    (orbPlane (D5.xB AM BM) UR 793590 5 c) = true := fun c hc => by
  have hs : c / 12 < 13 := by omega
  have h0 : orbNetOK RO.DS NX RO.PL (D5.xB AM BM) UR 793590 5 12 (c / 12) = true :=
    NBX.all (c / 12) hs
  have h := orbNetOK_sound h0 (c % 12) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem cntK1 : ((Finset.range 3968055).filter fun i => ∀ k ∈ D5.K1,
    rhoC (ptK RO.PL i) (wM D5.xw ^ k.1 *ᵥ ptK RO.PL i) = k.2).card = D5.s := by
  have e : (5 * 793590 + 105 : ℕ) = 3968055 := rfl
  have hf : Nat.beq (net RO.DS NX (full (5 * 793590 + 105))) (full (5 * 793590 + 105)) = true := by
    rw [e]
    exact nxFull
  have h := D5.card_prof_orb (PL := RO.PL) (Ds := RO.DS) (Ms := NX) (U := UR) (cs := cr)
    (m := 793590) (p := 5) (f := 105) (Q := 4) (d := 18) (rep_wM rep_A rep_B D5.xw) (by decide)
    (by norm_num) (lenN_leafPl _ _ _) nxOK hf nbAll (by norm_num) (fun q hq => CRX.all q hq)
    orbFix
  have e2 : 5 * ∑ q ∈ Finset.range 4, nthN cr q = D5.s := by decide +kernel
  rw [e, e2] at h
  exact h

theorem Lc : D5.LOK AM BM = true := by quickRfl

theorem Hc : D5.HOK AM BM = true := by quickRfl

theorem candI : D5.candIni AM BM = true := by quickRfl

@[expose] noncomputable def csegC (k : ℕ) : Bool := D5.csegZ AM BM CC 2 10 k 17

#kc_slices CFSG.KD.StdOdd.Cent.C5.CS CFSG.KD.StdOdd.Cent.C5.csegC 10

@[expose] noncomputable def segC (k : ℕ) : Bool := D5.segP AM BM CK 3 k

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
  centFacts_of_count D5 rep_A rep_B bits v0 v1 P.lines len
    (by decide) (by decide) (by decide) base LVK Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) cntK1 Hc candI
    (cand_of_csegs D5 (by decide) fun k hk => D5.csegF_of_csegH (D5.csegH_of_csegZ (CS.all k hk)))
    (start_of_segs D5 rep_A rep_B (by decide) fun k hk => segP_sound D5 (SG.all k hk))
    (by decide +kernel)
    (refs_of_flat D5 rep_A rep_B v0 v1 P.lines len base LVK (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 7) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C5

end CFSG.KD.StdOdd.Cent

end
