module

public import Certificates.Kernel.Item434.McLK
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelItem434

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Item434 CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Fischer
open CFSG.KC.B3S3K (cm pw)

theorem pMH {k : ℕ} (hk : k < 52) : Pk 275 9 (mclArr k) (MH.F k) := by
  refine ⟨?_, CFSG.KS.Raw.Orb.allN_iff.1 kMHp k hk⟩
  unfold mclArr
  rw [MH.eq]
  exact hexTable_sound MH.all k hk

theorem pM9 {k : ℕ} (hk : k < 3) : Pk 275 9 (mcl9Arr k) (M9.F k) := by
  refine ⟨?_, CFSG.KS.Raw.Orb.allN_iff.1 kM9p k hk⟩
  unfold mcl9Arr
  rw [M9.eq]
  exact hexTable_sound M9.all k hk

theorem pK3 {k : ℕ} (hk : k < 152) : Pk 275 9 (mcl3Arr k) (K3.F k) := by
  refine ⟨?_, CFSG.KS.Raw.Orb.allN_iff.1 kK3p k hk⟩
  unfold mcl3Arr
  rw [K3.eq]
  exact hexTable_sound K3.all k hk

theorem qsize : mcl3QGens.size = 4 := by simp [mcl3QGens]

theorem qgen_eq {k : ℕ} (hk : k < 4) : mcl3QGens[k]! = mcl3Arr (0 + k) := by
  unfold mcl3QGens
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem line_eq {j : ℕ} (hj : j < 148) : mcl3Lines[j]! = mcl3Arr (4 + j) := by
  unfold mcl3Lines
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem pDP (u : ℕ) (hu : u < 81) : Pk 275 9 (mclDProd u) (DP u) := by
  rw [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 kDP u hu)]
  unfold mclDProd dK
  exact pk_comp kW (pk_comp kW (pk_comp kW (pk_powN kW (pMH (by norm_num)) _)
    (pk_powN kW (pMH (by norm_num)) _)) (pk_powN kW (pMH (by norm_num)) _))
    (pk_powN kW (pMH (by norm_num)) _)

theorem pk_cjN {a b : Array ℕ} {p q : ℕ} (ha : Pk 275 9 a p) (hb : Pk 275 9 b q) :
    Pk 275 9 (conjN 275 a b) (cjN p q) :=
  pk_conjN kW ha hb

theorem mclSift_of {x : Array ℕ} {G : ℕ} (hx : Pk 275 9 x G) (h : siftM G = true) :
    mclSift x = true := by
  unfold siftM at h
  simp only [Bool.and_eq_true] at h
  unfold mclSift
  rw [isInvA_pk hx, Bool.true_and]
  exact siftK_soundR KernelCensus.McLK.binds KernelCensus.McLK.hperm KernelCensus.McLC.hl hx.1
    (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

theorem mclInD_of {x : Array ℕ} {X u : ℕ} (hx : Pk 275 9 x X) (hu : u < 81)
    (h : Nat.beq X (DP u) = true) : mclInD x = true := by
  unfold mclInD
  exact any_range_of u hu (by rw [eqA_pk kW hx (pDP u hu)]; exact h)

theorem mcl_z : mclZCheck = true := by
  unfold mclZCheck
  rw [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [eqA_pk kW (pMH (by norm_num)) (pk_id kW)]
    exact kZ.1
  · rw [qsize]
    refine allLt_of_allN kZ.2 fun k hk h => ?_
    rw [qgen_eq hk, Nat.zero_add, commN_pk kW (pMH (by norm_num)) (pK3 (by omega))]
    exact h

theorem mcl_d : mclDCheck = true := by
  unfold mclDCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact allLt_of_allN kD1 fun k hk h => mclSift_of (pMH (by omega)) h
  · refine allLt_of_allN kD2 fun k hk h => ?_
    rw [eqA_pk kW (pk_powN kW (pMH (by omega)) 3) (pk_id kW)]
    exact h
  · refine allLt_of_allN kD3 fun k hk h => allLt_of_allN h fun l hl h' => ?_
    rw [commN_pk kW (pMH (by omega)) (pMH (by omega))]
    exact h'
  · refine allLt_of_allN kD4 fun u hu h => allLt_of_allN h fun v hv h' => ?_
    rw [eqA_pk kW (pDP u hu) (pDP v hv)]
    exact h'

theorem enumQ : CFSG.RankThree.Native.enumOK 275 mcl3QGens mcl3Keys mcl3QCert = true ∧ mcl3QCert.pts.size = EQ.N ∧
    ∀ i < EQ.N, mcl3QCert.pts[i]! = unpack 275 9 (EQ.T i) := by
  have hk : mcl3Keys = CFSG.Sporadic.Schreier.PairMcL.baseArr.toList := rfl
  have bindQ : CFSG.KC.B3S3K.BindA 275 9 mcl3QGens EQ.ng EQ.G := by
    rw [Nat.eq_of_beq_eq_true kEQn.1]
    refine ⟨qsize, fun j hj => ?_⟩
    rw [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 kEQG j hj), qgen_eq hj, Nat.zero_add]
    exact (pK3 (by omega)).1
  have pQE : ∀ k < EQ.ng, permB 275 9 (EQ.G k) = true := by
    intro k hk
    rw [Nat.eq_of_beq_eq_true kEQn.1] at hk
    rw [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 kEQG k hk)]
    exact (pK3 (by omega)).2
  unfold mcl3QCert
  rw [hk]
  exact CFSG.KC.B3S3K.enum_of bindQ pQE EQ.ok (by decide) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true kEQn.2]; omega)

theorem kL (j : ℕ) (hj : j < 148) : lineK LW j = true := by
  rcases (by omega : j < 37 ∨ (37 ≤ j ∧ j < 74) ∨ (74 ≤ j ∧ j < 111) ∨ 111 ≤ j) with h | h | h | h
  · exact CFSG.KS.Raw.Orb.allN_iff.1 kL0 j h
  · have e := CFSG.KS.Raw.Orb.allN_iff.1 kL1 (j - 37) (by omega)
    rwa [Nat.add_sub_cancel' h.1] at e
  · have e := CFSG.KS.Raw.Orb.allN_iff.1 kL2 (j - 74) (by omega)
    rwa [Nat.add_sub_cancel' h.1] at e
  · have e := CFSG.KS.Raw.Orb.allN_iff.1 kL3 (j - 111) (by omega)
    rwa [Nat.add_sub_cancel' h] at e

theorem mcl_line : mclLineCheck = true := by
  obtain ⟨-, hN, hT⟩ := enumQ
  unfold mclLineCheck
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_
  dsimp only
  have hL := pK3 (k := 4 + j) (by omega)
  rw [line_eq hj]
  have h := kL j hj
  unfold lineK at h
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · left
    rw [Bool.and_eq_true] at h
    exact mclInD_of hL (Nat.blt_eq.mp h.1) h.2
  · right
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hk, hc⟩, hz⟩, hs⟩ := h
    have hk' := Nat.blt_eq.mp hk
    have hq : Pk 275 9 mcl3QCert.pts[(LW j - 81) / 24]! (EQ.T ((LW j - 81) / 24)) :=
      ⟨hT _ hk', CFSG.KS.Raw.Orb.allN_iff.1 EQ.perm _ hk'⟩
    refine any_range_of ((LW j - 81) / 24) (by rw [hN]; exact hk') ?_
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨any_range_of ((LW j - 81) % 24) (Nat.mod_lt _ (by norm_num)) ?_, ?_⟩,
      mclSift_of hq hs⟩
    · rw [eqA_pk kW (pk_cjN hq hL) (pMH (by omega))]
      exact hc
    · rw [eqA_pk kW (pk_cjN hq (pMH (by norm_num))) (pMH (by norm_num))]
      exact hz

theorem mcl_conj : mclConjCheck = true := by
  unfold mclConjCheck
  refine allLt_of_allN kC fun i hi h => ?_
  unfold conjK at h
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨hs, -⟩, hu⟩, hcu⟩, hz⟩, hcz⟩ := h
  have hH : Pk 275 9 (mclArr (28 + i)) (MH.F (28 + i)) := pMH (by omega)
  have hR : Pk 275 9 (mclArr (4 + i)) (MH.F (4 + i)) := pMH (by omega)
  exact ⟨⟨⟨mclSift_of hH hs, isInvA_pk hR⟩, mclInD_of (pk_cjN hH hR) (Nat.blt_eq.mp hu) hcu⟩,
    mclInD_of (pk_cjN hH (pMH (by norm_num))) (Nat.blt_eq.mp hz) hcz⟩

theorem pE0 : Pk 275 9 (mcl9E 0) (DP 34) := pDP 34 (by norm_num)
theorem pE1 : Pk 275 9 (mcl9E 1) (DP 3) := pDP 3 (by norm_num)
theorem pE2 : Pk 275 9 (mcl9E 2) (DP 38) := pDP 38 (by norm_num)
theorem pE3 : Pk 275 9 (mcl9E 3) (DP 35) := pDP 35 (by norm_num)

theorem pP9 (u : ℕ) (hu : u < 81) : Pk 275 9 (mcl9Prod u) (P9 u) := by
  rw [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 kP9 u hu)]
  unfold mcl9Prod p9K
  exact pk_comp kW (pk_comp kW (pk_comp kW (pk_powN kW pE0 _) (pk_powN kW pE1 _))
    (pk_powN kW pE2 _)) (pk_powN kW pE3 _)

theorem mcl9_ok : mcl9Check = true := by
  have r := k9R
  simp only [Bool.and_eq_true] at r
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8⟩, r9⟩ := r
  have s0 := pM9 (k := 0) (by norm_num)
  have s1 := pM9 (k := 1) (by norm_num)
  have s2 := pM9 (k := 2) (by norm_num)
  unfold mcl9Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact allLt_of_allN k9S fun k hk h => mclSift_of (pM9 hk) h
  · rw [eqA_pk kW (pk_cjN s0 pE0) pE0]
    exact r1
  · rw [eqA_pk kW (pk_cjN s0 pE1) pE1]
    exact r2
  · rw [eqA_pk kW (pk_cjN s0 pE2) (pk_powN kW pE2 2)]
    exact r3
  · rw [eqA_pk kW (pk_cjN s0 pE3) (pk_powN kW pE3 2)]
    exact r4
  · rw [eqA_pk kW (pk_cjN s1 pE0) pE0]
    exact r5
  · rw [eqA_pk kW (pk_cjN s1 pE1) (pk_powN kW pE1 2)]
    exact r6
  · rw [eqA_pk kW (pk_cjN s1 pE2) pE2]
    exact r7
  · rw [eqA_pk kW (pk_cjN s1 pE3) (pk_powN kW pE3 2)]
    exact r8
  · rw [eqA_pk kW (pk_cjN s2 pE1) (pP9 73 (by norm_num))]
    exact r9
  · refine allLt_of_allN k9D fun u hu h => allLt_of_allN h fun v hv h' => ?_
    rw [eqA_pk kW (pP9 u hu) (pP9 v hv)]
    exact h'

end CertificateChecks.KernelItem434

end
