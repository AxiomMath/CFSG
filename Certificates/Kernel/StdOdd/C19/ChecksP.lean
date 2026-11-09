module

public import Certificates.Kernel.StdOdd.C19.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
public import Certificates.Kernel.StdOdd.RootOrbit
public import Certificates.Kernel.StdOdd.C19.ChecksX
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

namespace C19

theorem v0 : Nat.beq (nthV D19.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D19.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D19.V) (Nat.add 2 (lenLL D19.prog)) = true := by quickRfl

theorem base : D19.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D19.levQZ 8640 (j + 1)

#kc_slices CFSG.KD.StdOdd.Cent.C19.LV CFSG.KD.StdOdd.Cent.C19.levF 18

theorem LVK : ∀ j < D19.p - 1, D19.LevFact (j + 1) := fun j hj =>
  levFact_of_levOK D19 (levQZ_sound D19 (LV.all j hj))

theorem nbAll : ∀ c < 156, Nat.beq (net RO.DS NX (nthN RO.PL c))
    (orbPlane (D19.xB AM BM) UR 208845 19 c) = true := fun c hc => by
  have hs : c / 12 < 13 := by omega
  have h0 : orbNetOK RO.DS NX RO.PL (D19.xB AM BM) UR 208845 19 12 (c / 12) = true :=
    NBX.all (c / 12) hs
  have h := orbNetOK_sound h0 (c % 12) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem cntK1 : ((Finset.range 3968055).filter fun i => ∀ k ∈ D19.K1,
    rhoC (ptK RO.PL i) (wM D19.xw ^ k.1 *ᵥ ptK RO.PL i) = k.2).card = D19.s := by
  have e : (19 * 208845 + 0 : ℕ) = 3968055 := rfl
  have hf : Nat.beq (net RO.DS NX (full (19 * 208845 + 0))) (full (19 * 208845 + 0)) = true := by
    rw [e]
    exact nxFull
  have h := D19.card_prof_orb (PL := RO.PL) (Ds := RO.DS) (Ms := NX) (U := UR) (cs := cr)
    (m := 208845) (p := 19) (f := 0) (Q := 1) (d := 18) (rep_wM rep_A rep_B D19.xw) (by decide)
    (by norm_num) (lenN_leafPl _ _ _) nxOK hf nbAll (by norm_num) (fun q hq => CRX.all q hq)
    orbFix
  have e2 : 19 * ∑ q ∈ Finset.range 1, nthN cr q = D19.s := by decide +kernel
  rw [e, e2] at h
  exact h

theorem Lc : D19.LOK AM BM = true := by quickRfl

theorem Hc : D19.HOK AM BM = true := by quickRfl

theorem cand : D19.candF AM BM = true := by quickRfl

@[expose] noncomputable def segC (k : ℕ) : Bool := D19.segP AM BM CK 3 k

#kc_slices CFSG.KD.StdOdd.Cent.C19.SG CFSG.KD.StdOdd.Cent.C19.segC 3

@[expose] noncomputable def RB : ℕ :=
  (List.range 19).foldl (fun a j => a + nthN rs j * nthN nl j) 0

@[expose] noncomputable def orbF (ri : ℕ) : List ℕ :=
  (List.range 19).map fun k => nthN orb (ri * 19 + k)

@[expose] noncomputable def stepF (ri : ℕ) : List (List (List ℕ)) :=
  levSteps (Nat.shiftRight RF (8 * RB * ri)) rs nl (nthN fail ri)

@[expose] noncomputable def rbC (ri : ℕ) : Bool :=
  D19.rbF AM BM (orbF ri) (nthN fail ri) (nthN sidx ri)

#kc_slices CFSG.KD.StdOdd.Cent.C19.RBS CFSG.KD.StdOdd.Cent.C19.rbC 2

@[expose] noncomputable def rcP (q : ℕ) : Bool :=
  flatC 18 3 (fun ri => nthN fail ri)
    (fun ri l k => D19.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k) q

#kc_slices CFSG.KD.StdOdd.Cent.C19.RCP CFSG.KD.StdOdd.Cent.C19.rcP 108

@[expose] noncomputable def rfC (ri : ℕ) : Bool := D19.rfinF RK 3 ri (orbF ri) (nthN fail ri)

#kc_slices CFSG.KD.StdOdd.Cent.C19.RFS CFSG.KD.StdOdd.Cent.C19.rfC 2

theorem cov : D19.covF (nthN sidx) 2 = true := by quickRfl

theorem RCF : ∀ q < 2 * ((D19.p - 1) * 3), flatC (D19.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D19.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k) q = true := fun q hq =>
  @flatC_mono (D19.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D19.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun ri l k => D19.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun a b c h => @rchP_sound D19 AM BM RK 3 a (orbF a) (stepF a) b c h) q (RCP.all q hq)

theorem facts19 : CentFacts D19.p 19 D19.xw D19.d0 D19.e D19.K1 D19.Kall :=
  centFacts_of_count D19 rep_A rep_B bits v0 v1 P.lines len
    (by decide) (by decide) (by decide) base LVK Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) cntK1 Hc
    (candWalk_of_candF D19 cand).1 (candWalk_of_candF D19 cand).2
    (start_of_segs D19 rep_A rep_B (by decide) fun k hk => segP_sound D19 (SG.all k hk))
    (by decide +kernel)
    (refs_of_flat D19 rep_A rep_B v0 v1 P.lines len base LVK (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 2) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C19

end CFSG.KD.StdOdd.Cent

end
