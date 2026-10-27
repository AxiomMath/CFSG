module

public import Certificates.Kernel.Sporadic.OddCore.SuzRFC
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.HeFixKFix
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzRF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.LocalR CFSG.ComponentClassification.AS81.SuzB0
  CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "T1" => SuzInvT1.F 0

theorem band {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := (bAnd_iff a b).1 h

theorem bif_t {c t e : Bool} (hc : c = true) (h : bIf(c, t, e) = true) : t = true := by
  subst hc
  exact h

theorem bif_f {c t e : Bool} (hc : c = false) (h : bIf(c, t, e) = true) : e = true := by
  subst hc
  exact h

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := CFSG.KS.Raw.Orb.strictB_eq y k

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem beqN (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · rw [Bool.eq_false_iff.2 (fun e => h (Nat.eq_of_beq_eq_true e))]
    simpa using h

theorem not_beq {a b : Nat} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem cover' {L N : Nat} {Q : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → Q i) : ∀ i < L * N, Q i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem pts {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat} {k cnt L N : Nat} (hL : 0 < L)
    (hc : cnt ≤ L * N)
    (h : ∀ s < N,
      penumSlK 1782 11 (mask 11) (1782 * 11) conj G GI k cnt T PL POS SRT SRI (L * s) L = true) :
    ∀ i < cnt, penumPtK 1782 11 (mask 11) (1782 * 11) conj G GI k cnt T PL POS SRT SRI i = true :=
  fun i hi => cover' (Q := fun i => i < cnt →
      penumPtK 1782 11 (mask 11) (1782 * 11) conj G GI k cnt T PL POS SRT SRI i = true) hL
    (fun s hs i h1 h2 hc' => penumSl_spec (h s hs) i h1 h2 hc') i (by omega) hi

theorem rec_tabs {n w cnt : Nat} {T PL : Nat → Nat} {i : Nat} (hi : i < cnt) :
    (penumRec n w cnt T PL).tabs[i]! = unpack n w (T i) := by
  rw [penumRec_eq]
  exact ofFn_get (fun i => unpack n w (T i)) hi

theorem pg_pc {X Y : Nat} (hX : cn X = true) (hY : cn Y = true) {p : Nat} (hp : p < 1782) :
    pgk (pc X Y) p = pgk X (pgk Y p) := by
  have e := compA_unpack hX hY
  have h1 : (unpack 1782 11 (pc X Y))[p]! = pgk (pc X Y) p := CFSG.KC.HeFixK.unpack_getElem! hp
  have h2 : (unpack 1782 11 X)[(unpack 1782 11 Y)[p]!]! = pgk X (pgk Y p) := by
    rw [CFSG.KC.HeFixK.unpack_getElem! hp,
      CFSG.KC.HeFixK.unpack_getElem! (CFSG.KC.HeFixK.pg_lt_of_canonK hY hp)]
  rw [← h1, ← e, CFSG.Monster.B.Co2.compA_get hp]
  exact h2

theorem pg_id {p : Nat} (hp : p < 1782) : pgk Id p = p := by
  have h : (unpack 1782 11 Id)[p]! = pgk Id p := CFSG.KC.HeFixK.unpack_getElem! hp
  rw [← h, ← pId'.1]
  simp [idTab, hp]

theorem invsOK_of {gens ginv : Array Tab} {G GI : Nat → Nat} {k : Nat}
    (hs : gens.size = k) (hsi : ginv.size = k) (hg : ∀ j < k, P gens[j]! (G j))
    (hgi : ∀ j < k, P ginv[j]! (GI j)) (h : allN k (fun j => Nat.beq (pc (GI j) (G j)) Id) = true) :
    invsOK 1782 gens ginv = true := by
  unfold invsOK
  rw [hs, hsi, beq_self_eq_true, Bool.true_and]
  refine allBelow_of fun j hj => ?_
  rw [sizeP (hgi j hj), beq_self_eq_true, Bool.true_and, beqP (pc' (hgi j hj) (hg j hj)) pId']
  exact allN_spec h j hj

theorem pLam {i : Nat} (hi : i < 4) : P (lambdaTab i) (lamK i) := by
  interval_cases i
  · exact pt1
  · have e2 : qProds[1]! = qProd 1 := by
      unfold qProds
      rw [getElem!_pos _ 1 (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
    change P qProds[1]! (qProdK 1)
    rw [e2]
    exact pqProd 1
  · exact cWord_P [1] (by decide)
  · exact cWord_P _ (by decide)

theorem pL4 : P (lambdaTab 3) L4 := pLam (i := 3) (by norm_num)

theorem pO {j : Nat} (hj : j < 2) : P orbGens[j]! (SuzInvT1.F (Nat.add 20 (Nat.mul 2 j))) := by
  interval_cases j
  · exact pC (k := 2) (by norm_num)
  · exact pC (k := 4) (by norm_num)

theorem pS {j : Nat} (hj : j < 4) : P s1Gens[j]! (sK j) := by
  have e : s1Gens[j]! = sylowGenTab (s1Idx.getD j 0) :=
    ofFn_get (fun j => sylowGenTab (s1Idx.getD j 0)) hj
  rw [e]
  interval_cases j
  · have e1 : sylowGenTab (s1Idx.getD 0 0) = qArr 0 := by simp [s1Idx, sylowGenTab]
    have e2 : sK 0 = KernelLC.SuzB0Q.F 0 := rfl
    rw [e1, e2]
    exact pQ (by norm_num)
  · have e1 : sylowGenTab (s1Idx.getD 1 0) = cWord [6] := by
      simp [s1Idx, sylowGenTab, sylowLiftWords]
    have e2 : sK 1 = cWK [6] := rfl
    rw [e1, e2]
    exact cWord_P [6] (by decide)
  · have e1 : sylowGenTab (s1Idx.getD 2 0) = cWord [7, 9, 2, 4] := by
      simp [s1Idx, sylowGenTab, sylowLiftWords]
    have e2 : sK 2 = cWK [7, 9, 2, 4] := rfl
    rw [e1, e2]
    exact cWord_P [7, 9, 2, 4] (by decide)
  · have e1 : sylowGenTab (s1Idx.getD 3 0) = cWord [3, 6, 5, 7] := by
      simp [s1Idx, sylowGenTab, sylowLiftWords]
    have e2 : sK 3 = cWK [3, 6, 5, 7] := rfl
    rw [e1, e2]
    exact cWord_P [3, 6, 5, 7] (by decide)

theorem orbGens_size : orbGens.size = 2 := rfl

theorem orbInvs_size : orbInvs.size = 2 := by simp [orbInvs, orbGens]

theorem gO {R : Nat} {G GI : Nat → Nat} {i : Nat} (hb : bindO R G GI i = true) :
    R = lamK i ∧ (∀ j < 2, P orbGens[j]! (G j)) ∧ (∀ j < 2, P orbInvs[j]! (GI j)) := by
  unfold bindO at hb
  obtain ⟨h1, h⟩ := band hb
  obtain ⟨h2, h⟩ := band h
  obtain ⟨h3, h⟩ := band h
  obtain ⟨h4, h⟩ := band h
  obtain ⟨h5, h⟩ := band h
  obtain ⟨h6, h7⟩ := band h
  have hg : ∀ j < 2, P orbGens[j]! (G j) := by
    intro j hj
    interval_cases j
    · exact p_eq (pO (j := 0) (by norm_num)) h2
    · exact p_eq (pO (j := 1) (by norm_num)) h3
  refine ⟨Nat.eq_of_beq_eq_true h1, hg, fun j hj => ?_⟩
  have e : orbInvs[j]! = invTab 1782 orbGens[j]! := map_get _ (by rw [orbGens_size]; exact hj)
  rw [e]
  interval_cases j
  · exact (p_invR (hg 0 (by norm_num)) h4 h6).1
  · exact (p_invR (hg 1 (by norm_num)) h5 h7).1

theorem orbit_ok {R cnt cap : Nat} {G GI T PL POS SRT SRI : Nat → Nat} {i : Nat} (hi : i < 4)
    (hb : bindO R G GI i = true) (hinv : allN 2 (fun j => Nat.beq (pc (GI j) (G j)) Id) = true)
    (hh : penumHdK R cnt cap T PL = true)
    (hp : ∀ j < cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true G GI 2 cnt T PL POS SRT SRI j =
      true) :
    orbitBFS 1782 orbGens orbInvs (lambdaTab i) cap = penumRec 1782 11 cnt T PL ∧
      orbitOK 1782 orbGens orbInvs (lambdaTab i) (penumRec 1782 11 cnt T PL) = true := by
  obtain ⟨hR, hg, hgi⟩ := gO hb
  have hx : lambdaTab i = unpack 1782 11 R := by
    rw [hR]
    exact (pLam hi).1
  have h := penumK_conj_sound kSz ⟨orbGens_size, hg⟩ ⟨orbInvs_size, hgi⟩ hx hh hp
  refine ⟨h.1, ?_⟩
  unfold orbitOK
  rw [invsOK_of orbGens_size orbInvs_size hg hgi hinv, h.2]
  rfl

theorem inv4 : allN 2 (fun j => Nat.beq (pc (SuzRFO0.GI j) (SuzRFO0.G j)) Id) = true ∧
    allN 2 (fun j => Nat.beq (pc (SuzRFO1.GI j) (SuzRFO1.G j)) Id) = true ∧
    allN 2 (fun j => Nat.beq (pc (SuzRFO2.GI j) (SuzRFO2.G j)) Id) = true ∧
    allN 2 (fun j => Nat.beq (pc (SuzRFO3.GI j) (SuzRFO3.G j)) Id) = true :=
  ⟨kInv0, kInv1, kInv2, kInv3⟩

theorem ptO0 : ∀ i < SuzRFO0.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SuzRFO0.G SuzRFO0.GI 2
    SuzRFO0.cnt SuzRFO0.T SuzRFO0.PL SuzRFO0.POS SuzRFO0.SRT SuzRFO0.SRI i = true :=
  pts (L := 6) (N := 1) (by norm_num) (by rw [kCnt.1]; norm_num) oSl0All

theorem ptO1 : ∀ i < SuzRFO1.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SuzRFO1.G SuzRFO1.GI 2
    SuzRFO1.cnt SuzRFO1.T SuzRFO1.PL SuzRFO1.POS SuzRFO1.SRT SuzRFO1.SRI i = true :=
  pts (L := 6) (N := 9) (by norm_num) (by rw [kCnt.2.1]) oSl1All

theorem ptO2 : ∀ i < SuzRFO2.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SuzRFO2.G SuzRFO2.GI 2
    SuzRFO2.cnt SuzRFO2.T SuzRFO2.PL SuzRFO2.POS SuzRFO2.SRT SuzRFO2.SRI i = true :=
  pts (L := 6) (N := 60) (by norm_num) (by rw [kCnt.2.2.1]) oSl2All

theorem ptO3 : ∀ i < SuzRFO3.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SuzRFO3.G SuzRFO3.GI 2
    SuzRFO3.cnt SuzRFO3.T SuzRFO3.PL SuzRFO3.POS SuzRFO3.SRT SuzRFO3.SRI i = true :=
  pts (L := 6) (N := 1080) (by norm_num) (by rw [kCnt.2.2.2.1]) oSl3All

theorem ptS : ∀ i < SuzRFS.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SuzRFS.G SuzRFS.GI 4
    SuzRFS.cnt SuzRFS.T SuzRFS.PL SuzRFS.POS SuzRFS.SRT SuzRFS.SRI i = true :=
  pts (L := 8) (N := 1024) (by norm_num) (by rw [kCnt.2.2.2.2]) sSlAll

theorem orb0 : orbitBFS 1782 orbGens orbInvs (lambdaTab 0) 1 =
      penumRec 1782 11 SuzRFO0.cnt SuzRFO0.T SuzRFO0.PL ∧
    orbitOK 1782 orbGens orbInvs (lambdaTab 0)
      (penumRec 1782 11 SuzRFO0.cnt SuzRFO0.T SuzRFO0.PL) = true :=
  orbit_ok (by norm_num) kB0 inv4.1 kHd0 ptO0

theorem orb1 : orbitBFS 1782 orbGens orbInvs (lambdaTab 1) 54 =
      penumRec 1782 11 SuzRFO1.cnt SuzRFO1.T SuzRFO1.PL ∧
    orbitOK 1782 orbGens orbInvs (lambdaTab 1)
      (penumRec 1782 11 SuzRFO1.cnt SuzRFO1.T SuzRFO1.PL) = true :=
  orbit_ok (by norm_num) kB1 inv4.2.1 kHd1 ptO1

theorem orb2 : orbitBFS 1782 orbGens orbInvs (lambdaTab 2) 360 =
      penumRec 1782 11 SuzRFO2.cnt SuzRFO2.T SuzRFO2.PL ∧
    orbitOK 1782 orbGens orbInvs (lambdaTab 2)
      (penumRec 1782 11 SuzRFO2.cnt SuzRFO2.T SuzRFO2.PL) = true :=
  orbit_ok (by norm_num) kB2 inv4.2.2.1 kHd2 ptO2

theorem orb3 : orbitBFS 1782 orbGens orbInvs (lambdaTab 3) 6480 =
      penumRec 1782 11 SuzRFO3.cnt SuzRFO3.T SuzRFO3.PL ∧
    orbitOK 1782 orbGens orbInvs (lambdaTab 3)
      (penumRec 1782 11 SuzRFO3.cnt SuzRFO3.T SuzRFO3.PL) = true :=
  orbit_ok (by norm_num) kB3 inv4.2.2.2 kHd3 ptO3

theorem rec_size {n w cnt : Nat} {T PL : Nat → Nat} : (penumRec n w cnt T PL).tabs.size = cnt := by
  simp [penumRec]

theorem orbits_true : orbits2Check = true := by
  unfold orbits2Check lambdaOrbit2
  refine allBelow_of fun i hi => ?_
  interval_cases i
  · change (orbitOK 1782 orbGens orbInvs (lambdaTab 0)
      (orbitBFS 1782 orbGens orbInvs (lambdaTab 0) 1) &&
        (orbitBFS 1782 orbGens orbInvs (lambdaTab 0) 1).tabs.size == 1) = true
    rw [orb0.1, orb0.2, rec_size, kCnt.1]
    rfl
  · change (orbitOK 1782 orbGens orbInvs (lambdaTab 1)
      (orbitBFS 1782 orbGens orbInvs (lambdaTab 1) 54) &&
        (orbitBFS 1782 orbGens orbInvs (lambdaTab 1) 54).tabs.size == 54) = true
    rw [orb1.1, orb1.2, rec_size, kCnt.2.1]
    rfl
  · change (orbitOK 1782 orbGens orbInvs (lambdaTab 2)
      (orbitBFS 1782 orbGens orbInvs (lambdaTab 2) 360) &&
        (orbitBFS 1782 orbGens orbInvs (lambdaTab 2) 360).tabs.size == 360) = true
    rw [orb2.1, orb2.2, rec_size, kCnt.2.2.1]
    rfl
  · change (orbitOK 1782 orbGens orbInvs (lambdaTab 3)
      (orbitBFS 1782 orbGens orbInvs (lambdaTab 3) 6480) &&
        (orbitBFS 1782 orbGens orbInvs (lambdaTab 3) 6480).tabs.size == 6480) = true
    rw [orb3.1, orb3.2, rec_size, kCnt.2.2.2.1]
    rfl

theorem gS : GensOK 1782 11 4 SuzRFS.G s1Gens :=
  ⟨by simp [s1Gens], fun j hj => p_eq (pS hj) (allN_spec kBS j hj)⟩

theorem sE : enumBFS 1782 s1Gens 8192 = penumRec 1782 11 SuzRFS.cnt SuzRFS.T SuzRFS.PL ∧
    enumOK 1782 s1Gens (penumRec 1782 11 SuzRFS.cnt SuzRFS.T SuzRFS.PL) = true :=
  penumK_left_sound kSz gS kHdS ptS

theorem canS {k : Nat} (hk : k < 8192) : cn (SuzRFS.T k) = true :=
  penumPt_canon (ptS k (by rw [kCnt.2.2.2.2]; exact hk))

theorem wEl {k : Nat} (hk : k < 8192) :
    covK (SuzRFS.T k) (wg SuzRFWC k) = true ∧ comK (SuzRFS.T k) (wg SuzRFWV k) = true := by
  have hs : k / 32 < 256 := by omega
  have h := allBlk_spec (wSlAll (k / 32) hs) (k % 32) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 32 (k / 32)) (k % 32) = k := Nat.div_add_mod k 32
  rw [e] at h
  have h2 : strictB (SuzRFS.T k) (fun X =>
      bAnd(covK X (wg SuzRFWC k), comK X (wg SuzRFWV k))) = true := h
  simp only [sB] at h2
  exact band h2

theorem cov_of {X c : Nat} (h : covK X c = true) :
    X = Id ∨ (∃ p < 1782, pgk X (pgk X p) ≠ p) ∨ (∃ i < 4, ∃ q < OC i, OT i q = X) := by
  unfold covK at h
  by_cases h0 : c = 0
  · have hb : Nat.beq c 0 = true := by rw [h0]; rfl
    exact Or.inl (Nat.eq_of_beq_eq_true (bif_t hb h))
  · have h' := bif_f (beq_false h0) h
    by_cases h1 : c < 2048
    · have h2 := bif_t (Nat.blt_eq.mpr h1) h'
      simp only [sB] at h2
      obtain ⟨hp, hn⟩ := band h2
      exact Or.inr (Or.inl ⟨_, Nat.blt_eq.mp hp, not_beq hn⟩)
    · have h2 := bif_f (Bool.eq_false_iff.2 fun e => h1 (Nat.blt_eq.mp e)) h'
      simp only [sB] at h2
      obtain ⟨hi, h3⟩ := band h2
      obtain ⟨hq, he⟩ := band h3
      exact Or.inr (Or.inr ⟨_, Nat.blt_eq.mp hi, _, Nat.blt_eq.mp hq, Nat.eq_of_beq_eq_true he⟩)

theorem com_of {X e : Nat} (hX : cn X = true) (h : comK X e = true) :
    Nat.beq (pc X L4) (pc L4 X) = Nat.beq e 0 := by
  unfold comK at h
  by_cases h0 : e = 0
  · have hb : Nat.beq e 0 = true := by rw [h0]; rfl
    rw [bif_t hb h, hb]
  · have h' := bif_f (beq_false h0) h
    simp only [sB] at h'
    obtain ⟨hp, hn⟩ := band h'
    have hp' := Nat.blt_eq.mp hp
    rw [beq_false h0]
    refine beq_false fun e' => not_beq hn ?_
    rw [← pg_pc hX pL4.2 hp', e', pg_pc pL4.2 hX hp']

theorem lot_get {i : Nat} (hi : i < 4) : lambdaOrbitTabs2[i]! = (lambdaOrbit2 i).tabs :=
  ofFn_get (fun i => (lambdaOrbit2 i).tabs) hi

theorem found_orb {i q X : Nat} (hi : i < 4) (hq : q < OC i) (hX : OT i q = X) :
    found (indexOf lambdaOrbitTabs2[i]!) lambdaOrbitTabs2[i]! (unpack 1782 11 X) = true := by
  rw [lot_get hi]
  interval_cases i
  · have e : lambdaOrbit2 0 = penumRec 1782 11 SuzRFO0.cnt SuzRFO0.T SuzRFO0.PL := orb0.1
    rw [e]
    exact penum_found_sound ptO0 hq hX
  · have e : lambdaOrbit2 1 = penumRec 1782 11 SuzRFO1.cnt SuzRFO1.T SuzRFO1.PL := orb1.1
    rw [e]
    exact penum_found_sound ptO1 hq hX
  · have e : lambdaOrbit2 2 = penumRec 1782 11 SuzRFO2.cnt SuzRFO2.T SuzRFO2.PL := orb2.1
    rw [e]
    exact penum_found_sound ptO2 hq hX
  · have e : lambdaOrbit2 3 = penumRec 1782 11 SuzRFO3.cnt SuzRFO3.T SuzRFO3.PL := orb3.1
    rw [e]
    exact penum_found_sound ptO3 hq hX

theorem cover_true :
    coverOK 1782 (penumRec 1782 11 SuzRFS.cnt SuzRFS.T SuzRFS.PL).tabs lambdaOrbitTabs2 = true := by
  unfold coverOK
  dsimp only
  refine allBelow_of fun k hk => ?_
  rw [rec_size, kCnt.2.2.2.2] at hk
  rw [rec_tabs (by rw [kCnt.2.2.2.2]; exact hk)]
  have hX := canS hk
  have hP : P (unpack 1782 11 (SuzRFS.T k)) (SuzRFS.T k) := ⟨rfl, hX⟩
  rcases cov_of (wEl hk).1 with h | ⟨p, hp, hne⟩ | ⟨i, hi, q, hq, he⟩
  · rw [beqP hP pId', h, Nat.beq_refl]
    rfl
  · have hsq : Nat.beq (pc (SuzRFS.T k) (SuzRFS.T k)) Id = false := by
      refine beq_false fun e => hne ?_
      rw [← pg_pc hX hX hp, e]
      exact pg_id hp
    rw [beqP (pc' hP hP) pId', hsq]
    simp
  · have hf := found_orb hi hq he
    have ha : anyBelow lambdaOrbitTabs2.size (fun i => found (lambdaOrbitTabs2.map indexOf)[i]!
        lambdaOrbitTabs2[i]! (unpack 1782 11 (SuzRFS.T k))) = true := by
      unfold anyBelow
      refine List.any_eq_true.2 ⟨i, List.mem_range.2 (by simpa [lambdaOrbitTabs2] using hi), ?_⟩
      rw [map_get _ (by simpa [lambdaOrbitTabs2] using hi)]
      exact hf
    rw [ha]
    simp

theorem sylow_true : sylow2Check = true := by
  unfold sylow2Check s1Enum
  rw [sE.1, sE.2, cover_true, rec_size, kCnt.2.2.2.2]
  rfl

theorem v0_filter : (List.range 8192).filter (fun k =>
    comp 1782 (unpack 1782 11 (SuzRFS.T k)) (lambdaTab 3) ==
      comp 1782 (lambdaTab 3) (unpack 1782 11 (SuzRFS.T k))) = SuzRFV := by
  rw [← sel_spec kSel]
  refine List.filter_congr fun k hk => ?_
  have hk' := List.mem_range.1 hk
  have hX := canS hk'
  have hP : P (unpack 1782 11 (SuzRFS.T k)) (SuzRFS.T k) := ⟨rfl, hX⟩
  rw [beqP (pc' hP pL4) (pc' pL4 hP)]
  exact com_of hX (wEl hk').2

theorem v0_list : s1V0 = (SuzRFV.map fun k => unpack 1782 11 (SuzRFS.T k)).toArray := by
  have hT : (penumRec 1782 11 SuzRFS.cnt SuzRFS.T SuzRFS.PL).tabs =
      Array.ofFn (n := SuzRFS.cnt) fun i => unpack 1782 11 (SuzRFS.T i.val) := rfl
  unfold s1V0 centTabs s1Enum
  rw [sE.1, hT, filter_ofFn SuzRFS.cnt (fun i => unpack 1782 11 (SuzRFS.T i)), kCnt.2.2.2.2,
    v0_filter]

theorem v0_mem {k : Nat} (hk : k ∈ SuzRFV) : k < 8192 := by
  rw [← sel_spec kSel, List.mem_filter, List.mem_range] at hk
  exact hk.1

theorem v0_size : s1V0.size = 512 := by
  rw [v0_list, List.size_toArray, List.length_map, kVLen]

theorem v0_get {j : Nat} (hj : j < 512) : P s1V0[j]! (VT j) := by
  have hl : j < SuzRFV.length := by rw [kVLen]; exact hj
  have hn : CFSG.KS.Mathieu.nget SuzRFV j = SuzRFV[j] := CFSG.KS.PEnum.nget_get SuzRFV hl
  have hm : SuzRFV[j] < 8192 := v0_mem (List.getElem_mem hl)
  have e : s1V0[j]! = unpack 1782 11 (VT j) := by
    rw [v0_list, getElem!_pos _ j (by simpa using hl)]
    simp only [List.getElem_toArray, List.getElem_map]
    unfold VT
    rw [hn]
  rw [e]
  refine ⟨rfl, ?_⟩
  unfold VT
  rw [hn]
  exact canS hm

theorem p4_P {a : Array Nat} {A : Nat} (ha : P a A) : P (pow4Tab a) (p4 A) := by
  unfold pow4Tab p4
  rw [sN]
  exact pc' (pc' ha ha) (pc' ha ha)

theorem v0_true : v02Check = true := by
  have hp : ∀ j < 512, p4OK (VT j) = true := fun j hj => by
    have hs : j / 16 < 32 := by omega
    have h := allBlk_spec (pSlAll (j / 16) hs) (j % 16) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul 16 (j / 16)) (j % 16) = j := Nat.div_add_mod j 16
    rw [e] at h
    exact h
  have h1 : (allBelow 512 fun j => pow4Tab s1V0[j]! == idTab 1782 || pow4Tab s1V0[j]! == tTab) =
      true := by
    refine allBelow_of fun j hj => ?_
    have h : bIf(Nat.beq (p4 (VT j)) Id, true, Nat.beq (p4 (VT j)) T1) = true := by
      have h0 := hp j hj
      unfold p4OK at h0
      simp only [sB] at h0
      exact h0
    rw [beqP (p4_P (v0_get hj)) pId', beqP (p4_P (v0_get hj)) pt1]
    cases hz : Nat.beq (p4 (VT j)) Id
    · rw [bif_f (c := Nat.beq (p4 (VT j)) Id) (t := true) (e := Nat.beq (p4 (VT j)) T1) hz h]
      rfl
    · rfl
  have h2 : (anyBelow 512 fun j => pow4Tab s1V0[j]! == tTab) = true := by
    have ha := kAnyLt
    have hb := kAny
    generalize CFSG.KS.Mathieu.nget SuzRFA 0 = j0 at ha hb
    have hj := Nat.blt_eq.mp ha
    unfold anyBelow
    refine List.any_eq_true.2 ⟨j0, List.mem_range.2 hj, ?_⟩
    have e := beqP (p4_P (v0_get hj)) pt1
    exact e.trans hb
  unfold v02Check
  rw [v0_size, h1, h2]
  rfl

theorem lift_lt (m : Nat) : ∀ k ∈ sylowLiftWords.getD m [], k < 10 := by
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> decide
  · rw [List.getD_eq_default _ _ (by simpa [sylowLiftWords] using hm)]
    simp

theorem pSyl (j : Nat) : ∃ A, P (sylowGenTab j) A := by
  unfold sylowGenTab
  split_ifs with h1 h2
  · exact ⟨_, pQ h1⟩
  · exact ⟨_, pt1⟩
  · exact ⟨_, cWord_P _ (lift_lt _)⟩

theorem qP (v : Nat) (hv : v < 64) : P qProds[v]! (qProdK v) := by
  have e : qProds[v]! = qProd v := by
    unfold qProds
    rw [getElem!_pos _ v (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
  rw [e]
  exact pqProd v

theorem sizes_true : sizesCheck = true := by
  unfold sizesCheck
  have h1 : (allBelow 10 fun k => (cTab k).size == 1782) = true :=
    allBelow_of fun k hk => by rw [sizeP (pC hk)]; rfl
  have h2 : (allBelow 4 fun i => (lambdaTab i).size == 1782) = true :=
    allBelow_of fun i hi => by rw [sizeP (pLam hi)]; rfl
  have h3 : (allBelow 13 fun j => (sylowGenTab j).size == 1782) = true :=
    allBelow_of fun j _ => by
      obtain ⟨A, hA⟩ := pSyl j
      rw [sizeP hA]
      rfl
  rw [h1, h2, h3, sizeP (qP 4 (by norm_num)), sizeP (qP 8 (by norm_num))]
  rfl

theorem pOW (w : List Nat) (hw : ∀ k ∈ w, k < 2) : P (orbWord w) (oWK w) :=
  wP (gens := orbGens) (G := fun k => SuzInvT1.F (Nat.add 20 (Nat.mul 2 k)))
    (fun k hk => pO (by rw [orbGens_size] at hk; exact hk)) w
    (fun k hk => by rw [orbGens_size]; exact hw k hk)

theorem gen_true : genCheck = true := by
  unfold genCheck
  refine allBelow_of fun k hk => ?_
  have h := genKAll k hk
  unfold genK at h
  obtain ⟨h1, h2⟩ := band h
  have hw : ∀ a ∈ cBackWords.getD k [], a < 2 := by
    intro a ha
    have := List.all_eq_true.1 h1 a ha
    simpa using this
  rw [h1, Bool.true_and, beqP (pOW _ hw) (pC hk)]
  exact h2

theorem reps_true : repsCheck = true := by
  unfold repsCheck
  have h1 : (allBelow 4 fun i => comp 1782 (lambdaTab i) (lambdaTab i) == idTab 1782 &&
      !(lambdaTab i == idTab 1782) && fixedCount (lambdaTab i) == lambdaFixed[i]!) = true := by
    refine allBelow_of fun i hi => ?_
    have h := allN_spec kReps i hi
    simp only [sB] at h
    obtain ⟨ha, h'⟩ := band h
    obtain ⟨hb, hc⟩ := band h'
    have hf : lambdaFixed[i]! = fixN i := by interval_cases i <;> rfl
    have hfc : fixedCount (lambdaTab i) = OddCore.fixCntK 1782 11 (mask 11) (lamK i) := by
      rw [(pLam hi).1]
      exact OddCore.fixedCount_unpack
    rw [beqP (pc' (pLam hi) (pLam hi)) pId', beqP (pLam hi) pId', hfc, hf, beqN, ha, hc]
    simp only [Bool.true_and, Bool.and_true]
    exact hb
  have q4 := qP 4 (by norm_num)
  have q8 := qP 8 (by norm_num)
  have l1 := pLam (i := 1) (by norm_num)
  rw [h1, beqP (pc' q4 q4) pId', beqP (pc' q8 q8) pId', beqP (pc' q4 l1) (pc' l1 q4),
    beqP (pc' q8 l1) (pc' l1 q8), beqP (pc' (pc' (pc' q4 q8) q4) q8) pt1]
  rw [kQ1, kQ2, kQ3, kQ4, kQ5]
  rfl

end CertificateChecks.KernelSpor.SuzRF

end
