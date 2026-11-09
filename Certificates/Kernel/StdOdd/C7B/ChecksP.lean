module

public import Certificates.Kernel.StdOdd.C7B.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
public import Certificates.Kernel.StdOdd.CentPopH
public import Certificates.Kernel.StdOdd.RootOrbit
public import Certificates.Kernel.StdOdd.C7B.ChecksX
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

namespace C7B

theorem v0 : Nat.beq (nthV D7B.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D7B.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D7B.V) (Nat.add 2 (lenLL D7B.prog)) = true := by quickRfl

theorem base : D7B.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D7B.levQ 8640 (j + 2)

#kc_slices CFSG.KD.StdOdd.Cent.C7B.LV CFSG.KD.StdOdd.Cent.C7B.levF 5

theorem LI1 : D7B.levIni 1 = true := by quickRfl

@[expose] noncomputable def lsegC1 (k : ℕ) : Bool := D7B.lsegZ 1 LC1 4 7 k

#kc_slices CFSG.KD.StdOdd.Cent.C7B.LS1 CFSG.KD.StdOdd.Cent.C7B.lsegC1 7

theorem LVK : ∀ j < D7B.p - 1, D7B.LevFact (j + 1)
  | 0, _ => levFact_of_segs D7B (cc := LC1) (g := 4) LI1 (by decide) fun k hk =>
      D7B.lsegF_of_lsegZ (LS1.all k hk)
  | j + 1, hj => levFact_of_levOK D7B (levQ_sound D7B (LV.all j (by
      have : D7B.p = 7 := rfl
      change j < 5
      omega)))

theorem nbAll : ∀ c < 156, Nat.beq (net RO.DS NX (nthN RO.PL c))
    (orbPlane (D7B.xB AM BM) UR 566862 7 c) = true := fun c hc => by
  have hs : c / 12 < 13 := by omega
  have h0 : orbNetOK RO.DS NX RO.PL (D7B.xB AM BM) UR 566862 7 12 (c / 12) = true :=
    NBX.all (c / 12) hs
  have h := orbNetOK_sound h0 (c % 12) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem cntK1 : ((Finset.range 3968055).filter fun i => ∀ k ∈ D7B.K1,
    rhoC (ptK RO.PL i) (wM D7B.xw ^ k.1 *ᵥ ptK RO.PL i) = k.2).card = D7B.s := by
  have e : (7 * 566862 + 21 : ℕ) = 3968055 := rfl
  have hf : Nat.beq (net RO.DS NX (full (7 * 566862 + 21))) (full (7 * 566862 + 21)) = true := by
    rw [e]
    exact nxFull
  have h := D7B.card_prof_orb (PL := RO.PL) (Ds := RO.DS) (Ms := NX) (U := UR) (cs := cr)
    (m := 566862) (p := 7) (f := 21) (Q := 3) (d := 18) (rep_wM rep_A rep_B D7B.xw) (by decide)
    (by norm_num) (lenN_leafPl _ _ _) nxOK hf nbAll (by norm_num) (fun q hq => CRX.all q hq)
    orbFix
  have e2 : 7 * ∑ q ∈ Finset.range 3, nthN cr q = D7B.s := by decide +kernel
  rw [e, e2] at h
  exact h

theorem Lc : D7B.LOK AM BM = true := by quickRfl

theorem Hc : D7B.HOK AM BM = true := by quickRfl

theorem candI : D7B.candIni AM BM = true := by quickRfl

@[expose] noncomputable def csegC (k : ℕ) : Bool := D7B.csegZ AM BM CC 7 3 k 15

#kc_slices CFSG.KD.StdOdd.Cent.C7B.CS CFSG.KD.StdOdd.Cent.C7B.csegC 3

@[expose] noncomputable def segC (k : ℕ) : Bool := D7B.segP AM BM CK 3 k

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
  centFacts_of_count D7B rep_A rep_B bits v0 v1 P.lines len
    (by decide) (by decide) (by decide) base LVK Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) cntK1 Hc candI
    (cand_of_csegs D7B (by decide) fun k hk => D7B.csegF_of_csegH (D7B.csegH_of_csegZ (CS.all k hk)))
    (start_of_segs D7B rep_A rep_B (by decide) fun k hk => segP_sound D7B (SG.all k hk))
    (by decide +kernel)
    (refs_of_flat D7B rep_A rep_B v0 v1 P.lines len base LVK (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 29) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C7B

end CFSG.KD.StdOdd.Cent

end
