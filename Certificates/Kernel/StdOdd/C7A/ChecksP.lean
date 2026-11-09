module

public import Certificates.Kernel.StdOdd.C7A.Data
public import Certificates.Kernel.StdOdd.CentRefPSound
public import Certificates.Kernel.StdOdd.CentPopH
public import Certificates.Kernel.StdOdd.RootOrbit
public import Certificates.Kernel.StdOdd.C7A.ChecksX
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

namespace C7A

theorem v0 : Nat.beq (nthV D7A.V 0) AM = true := by quickRfl

theorem v1 : Nat.beq (nthV D7A.V 1) BM = true := by quickRfl

theorem len : Nat.beq (lenN D7A.V) (Nat.add 2 (lenLL D7A.prog)) = true := by quickRfl

theorem base : D7A.baseOK AM BM = true := by quickRfl

@[expose] noncomputable def levF (j : ℕ) : Bool := D7A.levQ 8640 (j + 2)

#kc_slices CFSG.KD.StdOdd.Cent.C7A.LV CFSG.KD.StdOdd.Cent.C7A.levF 5

theorem LI1 : D7A.levIni 1 = true := by quickRfl

@[expose] noncomputable def lsegC1 (k : ℕ) : Bool := D7A.lsegZ 1 LC1 4 7 k

#kc_slices CFSG.KD.StdOdd.Cent.C7A.LS1 CFSG.KD.StdOdd.Cent.C7A.lsegC1 7

theorem LVK : ∀ j < D7A.p - 1, D7A.LevFact (j + 1)
  | 0, _ => levFact_of_segs D7A (cc := LC1) (g := 4) LI1 (by decide) fun k hk =>
      D7A.lsegF_of_lsegZ (LS1.all k hk)
  | j + 1, hj => levFact_of_levOK D7A (levQ_sound D7A (LV.all j (by
      have : D7A.p = 7 := rfl
      change j < 5
      omega)))

theorem nbAll : ∀ c < 156, Nat.beq (net RO.DS NX (nthN RO.PL c))
    (orbPlane (D7A.xB AM BM) UR 566865 7 c) = true := fun c hc => by
  have hs : c / 12 < 13 := by omega
  have h0 : orbNetOK RO.DS NX RO.PL (D7A.xB AM BM) UR 566865 7 12 (c / 12) = true :=
    NBX.all (c / 12) hs
  have h := orbNetOK_sound h0 (c % 12) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem cntK1 : ((Finset.range 3968055).filter fun i => ∀ k ∈ D7A.K1,
    rhoC (ptK RO.PL i) (wM D7A.xw ^ k.1 *ᵥ ptK RO.PL i) = k.2).card = D7A.s := by
  have e : (7 * 566865 + 0 : ℕ) = 3968055 := rfl
  have hf : Nat.beq (net RO.DS NX (full (7 * 566865 + 0))) (full (7 * 566865 + 0)) = true := by
    rw [e]
    exact nxFull
  have h := D7A.card_prof_orb (PL := RO.PL) (Ds := RO.DS) (Ms := NX) (U := UR) (cs := cr)
    (m := 566865) (p := 7) (f := 0) (Q := 3) (d := 18) (rep_wM rep_A rep_B D7A.xw) (by decide)
    (by norm_num) (lenN_leafPl _ _ _) nxOK hf nbAll (by norm_num) (fun q hq => CRX.all q hq)
    orbFix
  have e2 : 7 * ∑ q ∈ Finset.range 3, nthN cr q = D7A.s := by decide +kernel
  rw [e, e2] at h
  exact h

theorem Lc : D7A.LOK AM BM = true := by quickRfl

theorem Hc : D7A.HOK AM BM = true := by quickRfl

theorem candI : D7A.candIni AM BM = true := by quickRfl

@[expose] noncomputable def csegC (k : ℕ) : Bool := D7A.csegZ AM BM CC 8 3 k 15

#kc_slices CFSG.KD.StdOdd.Cent.C7A.CS CFSG.KD.StdOdd.Cent.C7A.csegC 3

@[expose] noncomputable def segC (k : ℕ) : Bool := D7A.segP AM BM CK 3 k

#kc_slices CFSG.KD.StdOdd.Cent.C7A.SG CFSG.KD.StdOdd.Cent.C7A.segC 3

@[expose] noncomputable def RB : ℕ :=
  (List.range 7).foldl (fun a j => a + nthN rs j * nthN nl j) 0

@[expose] noncomputable def orbF (ri : ℕ) : List ℕ :=
  (List.range 7).map fun k => nthN orb (ri * 7 + k)

@[expose] noncomputable def stepF (ri : ℕ) : List (List (List ℕ)) :=
  levSteps (Nat.shiftRight RF (8 * RB * ri)) rs nl (nthN fail ri)

@[expose] noncomputable def rbC (ri : ℕ) : Bool :=
  D7A.rbF AM BM (orbF ri) (nthN fail ri) (nthN sidx ri)

#kc_slices CFSG.KD.StdOdd.Cent.C7A.RBS CFSG.KD.StdOdd.Cent.C7A.rbC 1

@[expose] noncomputable def rcP (q : ℕ) : Bool :=
  flatC 6 3 (fun ri => nthN fail ri)
    (fun ri l k => D7A.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k) q

#kc_slices CFSG.KD.StdOdd.Cent.C7A.RCP CFSG.KD.StdOdd.Cent.C7A.rcP 18

@[expose] noncomputable def rfC (ri : ℕ) : Bool := D7A.rfinF RK 3 ri (orbF ri) (nthN fail ri)

#kc_slices CFSG.KD.StdOdd.Cent.C7A.RFS CFSG.KD.StdOdd.Cent.C7A.rfC 1

theorem cov : D7A.covF (nthN sidx) 1 = true := by quickRfl

theorem RCF : ∀ q < 1 * ((D7A.p - 1) * 3), flatC (D7A.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D7A.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k) q = true := fun q hq =>
  @flatC_mono (D7A.p - 1) 3 (fun ri => nthN fail ri)
    (fun ri l k => D7A.rchP AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun ri l k => D7A.rchF AM BM RK 3 ri (orbF ri) (stepF ri) l k)
    (fun a b c h => @rchP_sound D7A AM BM RK 3 a (orbF a) (stepF a) b c h) q (RCP.all q hq)

theorem facts7A : CentFacts D7A.p 141120 D7A.xw D7A.d0 D7A.e D7A.K1 D7A.Kall :=
  centFacts_of_count D7A rep_A rep_B bits v0 v1 P.lines len
    (by decide) (by decide) (by decide) base LVK Lc (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) cntK1 Hc candI
    (cand_of_csegs D7A (by decide) fun k hk => D7A.csegF_of_csegH (D7A.csegH_of_csegZ (CS.all k hk)))
    (start_of_segs D7A rep_A rep_B (by decide) fun k hk => segP_sound D7A (SG.all k hk))
    (by decide +kernel)
    (refs_of_flat D7A rep_A rep_B v0 v1 P.lines len base LVK (by decide)
      (by decide) (by decide) (RK := RK) (K := 3) (R := 1) (by decide) (O := orbF) (Sr := stepF)
      (fl := fun ri => nthN fail ri) (sidx := fun ri => nthN sidx ri) (fun ri hri => RBS.all ri hri)
      RCF (fun ri hri => RFS.all ri hri) cov)

end C7A

end CFSG.KD.StdOdd.Cent

end
