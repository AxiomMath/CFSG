module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EQ0
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EQ1
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZ0
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZ1
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZ2
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzC1EZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.Sporadic.SuzRecog.C1ModelData CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1BF CertificateChecks.KernelSpor.SuzC1EG
  CertificateChecks.KernelSpor.SuzC1EF CertificateChecks.KernelSpor.SuzC1EV

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "W0" => SuzTwG 6

theorem kBindH : allN 2 (fun i => Nat.beq (SuzC1EH i) (decK (ce3Decs.getD i ([], 0)))) = true := by
  quickRfl

theorem kE3 : allN 2 (fun i => strictB e3K fun E =>
    Nat.beq (pc (SuzC1EH i) E) (pc E (SuzC1EH i))) = true := by quickRfl

theorem kBindQ : allN 3 (fun i => Nat.beq (SuzC1EQ.G i) (wK SuzC1EH (ct0Words.getD i [])) &&
    cK (SuzC1EQ.G i)) = true := by quickRfl

theorem kHdQ : penumHdK Id SuzC1EQ.cnt 192 SuzC1EQ.T SuzC1EQ.PL = true := by quickRfl

theorem kHdA : penumHdK Id SuzC1EA.cnt 12 SuzC1EA.T SuzC1EA.PL = true := by quickRfl

theorem kSlA : penumSlK 1782 11 (mask 11) (1782 * 11) false SuzC1EA.G SuzC1EA.GI 2 SuzC1EA.cnt
    SuzC1EA.T SuzC1EA.PL SuzC1EA.POS SuzC1EA.SRT SuzC1EA.SRI 0 12 = true := by quickRfl

theorem kDist : allN 48 (fun a => allN a fun b =>
    !(allBelow 4 fun i => Nat.beq (SuzC1EY (4 * a + i)) (SuzC1EY (4 * b + i)))) = true := by
  quickRfl

theorem kR1 : allN 16 (fun i => strictB (SuzC1EV.T (SuzC1EC.getD i 0)) fun C =>
    Nat.beq (pc C (SuzC1BT 11)) (pc (SuzC1BT 11) C)) = true := by quickRfl

theorem kCnt : SuzC1EQ.cnt = 192 ∧ SuzC1EA.cnt = 12 := ⟨rfl, rfl⟩

theorem negDist : Bool.not (allN 48 (fun a => allN a fun b =>
    !(allBelow 4 fun i => Nat.beq (SuzC1EY (4 * a + i))
      (SuzC1EY (if a = 7 ∧ b = 3 then 4 * a + i else 4 * b + i))))) = true := by quickRfl

theorem negA4 : Bool.not (Nat.beq (cntK a4q 3) 13) = true := by
  rw [Nat.eq_of_beq_eq_true kA4]
  rfl

theorem pH {i : Nat} (hi : i < 2) : P ce3Tabs[i]! (SuzC1EH i) := by
  rw [show ce3Tabs[i]! = ce3Tab i from ofFn_get _ hi]
  exact p_eq (pCE3 i) (allN_spec kBindH i hi)

theorem pHs : ∀ k < ce3Tabs.size, P ce3Tabs[k]! (SuzC1EH k) := fun k hk =>
  pH (by simpa [ce3Tabs] using hk)

theorem letters_ok {w : List Nat} (hw : ∀ k ∈ w, k < 2) : ∀ k ∈ w, k < ce3Tabs.size := by
  simpa [ce3Tabs] using hw

theorem ct0Words_ok {i : Nat} (hi : i < 3) : ∀ k ∈ ct0Words.getD i [], k < 2 := by
  interval_cases i <;> decide

theorem cosWords_ok (a : Nat) : ∀ k ∈ cosWords.getD a [], k < 2 := by
  rcases Nat.lt_or_ge a 48 with h | h
  · interval_cases a <;> decide
  · rw [List.getD_eq_default _ _ (by simp [cosWords]; omega)]
    decide

theorem pQG {i : Nat} (hi : i < 3) : P ct0Gens[i]! (SuzC1EQ.G i) := by
  rw [show ct0Gens[i]! = ct0Tab i from ofFn_get _ hi]
  exact p_eq (wP pHs _ (letters_ok (ct0Words_ok hi))) (and2 (allN_spec kBindQ i hi)).1

theorem gQ : GensOK 1782 11 3 SuzC1EQ.G ct0Gens := ⟨by simp [ct0Gens], fun _ hj => pQG hj⟩

theorem ptQ : ∀ i < SuzC1EQ.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SuzC1EQ.G SuzC1EQ.GI
    3 SuzC1EQ.cnt SuzC1EQ.T SuzC1EQ.PL SuzC1EQ.POS SuzC1EQ.SRT SuzC1EQ.SRI i = true := by
  intro i hi
  rw [kCnt.1] at hi
  rcases Nat.lt_or_ge i 96 with h | h
  · exact penumSl_spec slQ0 i (Nat.zero_le _) (by omega) (by rw [kCnt.1]; exact hi)
  · exact penumSl_spec slQ1 i h (by omega) (by rw [kCnt.1]; exact hi)

theorem ct0E : ct0Enum = penumRec 1782 11 SuzC1EQ.cnt SuzC1EQ.T SuzC1EQ.PL ∧
    enumOK 1782 ct0Gens (penumRec 1782 11 SuzC1EQ.cnt SuzC1EQ.T SuzC1EQ.PL) = true :=
  penumK_left_sound kSz gQ kHdQ ptQ

theorem ptA : ∀ i < SuzC1EA.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SuzC1EA.G SuzC1EA.GI
    2 SuzC1EA.cnt SuzC1EA.T SuzC1EA.PL SuzC1EA.POS SuzC1EA.SRT SuzC1EA.SRI i = true :=
  fun i hi => penumSl_spec kSlA i (Nat.zero_le _) (by rw [kCnt.2] at hi; omega) hi

theorem a4E : a4Enum = penumRec 1782 11 SuzC1EA.cnt SuzC1EA.T SuzC1EA.PL ∧
    enumOK 1782 #[w0T, rhoT] (penumRec 1782 11 SuzC1EA.cnt SuzC1EA.T SuzC1EA.PL) = true :=
  penumK_left_sound kSz gA4 kHdA ptA

theorem pJ {a : Nat} (ha : a < 48) : P cosTabs[a]! (SuzC1EJ a) := by
  rw [show cosTabs[a]! = cosTab a from ofFn_get _ ha]
  have h := allN_spec kCos a ha
  unfold cosK at h
  simp only [Bool.and_eq_true] at h
  exact p_eq (wP pHs _ (letters_ok (cosWords_ok a))) h.1.1.1

theorem pJI {a : Nat} (ha : a < 48) : P cosInvs[a]! (SuzC1EJI a) := by
  rw [show cosInvs[a]! = invTab 1782 cosTabs[a]! from map_get _ (by simpa [cosTabs] using ha)]
  have h := allN_spec kCos a ha
  unfold cosK at h
  simp only [Bool.and_eq_true] at h
  exact (p_invR (pJ ha) h.1.1.2 h.1.2).1

theorem pKey {a i : Nat} (ha : a < 48) (hi : i < 4) : P (cosKey a i) (SuzC1EY (4 * a + i)) := by
  unfold cosKey conjTab
  exact p_eq (pc' (pc' (pJ ha) (pT0 hi)) (pJI ha)) (allN_spec (allN_spec kKey a ha) i hi)

theorem pQT {i : Nat} (hi : i < 192) : P ct0Enum.tabs[i]! (SuzC1EQ.T i) := by
  refine ⟨?_, penumPt_canon (ptQ i (by rw [kCnt.1]; exact hi))⟩
  rw [ct0E.1]
  exact ofFn_get (fun i => unpack 1782 11 (SuzC1EQ.T i)) (by rw [kCnt.1]; exact hi)

theorem filter_size {p : Tab → Bool} {q : Nat → Bool}
    (hq : ∀ i < 192, p (unpack 1782 11 (SuzC1EQ.T i)) = q i) :
    (ct0Tabs.filter p).size = cntK q 3 := by
  unfold ct0Tabs
  rw [ct0E.1, penumRec_eq]
  simp only
  rw [kCnt.1, filter_ofFn 192 (fun i => unpack 1782 11 (SuzC1EQ.T i)), cntK_eq, List.size_toArray,
    List.length_map,
    ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro i hi
  rw [hq i (List.mem_range.1 hi)]

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · rw [h, beq_self_eq_true, Nat.beq_refl]
  · rw [beq_eq_false_iff_ne.2 h, beq_false h]

theorem a4_size : a4Tabs.size = 12 := by
  unfold a4Tabs
  rw [filter_size (q := a4q) fun i hi => ?_, Nat.eq_of_beq_eq_true kA4]
  have hP : P (unpack 1782 11 (SuzC1EQ.T i)) (SuzC1EQ.T i) :=
    ⟨rfl, penumPt_canon (ptQ i (by rw [kCnt.1]; exact hi))⟩
  unfold a4q
  rw [CFSG.KS.Raw.Orb.strictB_eq]
  exact beqP (pc' hP pz) (pc' pz hP)

theorem y_size : yTabs.size = 24 := by
  unfold yTabs
  rw [filter_size (q := yq) fun i hi => ?_, Nat.eq_of_beq_eq_true kY]
  have hP : P (unpack 1782 11 (SuzC1EQ.T i)) (SuzC1EQ.T i) :=
    ⟨rfl, penumPt_canon (ptQ i (by rw [kCnt.1]; exact hi))⟩
  unfold yq isY
  rw [CFSG.KS.Raw.Orb.strictB_eq, beqP (pc' hP hP) pId', beqP hP pId', fixedCount_eq', nat_beq]

theorem centCheck_true : centCheck = true := by
  unfold centCheck
  refine andT (andT (andT (andT (andT (andT (andT (andT (andT (andT (andT ?_ ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_) ?_
  · refine allBelow_of fun i hi => ?_
    rw [beqP (pc' (pH hi) pe3) (pc' pe3 (pH hi))]
    have h := allN_spec kE3 i hi
    rwa [CFSG.KS.Raw.Orb.strictB_eq] at h
  · rw [ct0E.1]
    exact ct0E.2
  · rw [ct0E.1]
    simp [penumRec, kCnt.1]
  · refine allBelow_of fun i hi => ?_
    rw [(pQG hi).1, commT0_unpack (pQG hi).2]
    exact (and2 (allN_spec kBindQ i hi)).2
  · refine invsOK_of (by simp [cosTabs]) (by simp [cosInvs, cosTabs]) (fun _ ha => pJ ha)
      (fun _ ha => pJI ha) (allN_of fun a ha => ?_)
    have h := allN_spec kCos a ha
    unfold cosK at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  · refine allBelow_of fun a ha => allBelow_of fun b hb => ?_
    have hb' : b < 48 := by omega
    have e : (allBelow 4 fun i => cosKey a i == cosKey b i) =
        allBelow 4 fun i => Nat.beq (SuzC1EY (4 * a + i)) (SuzC1EY (4 * b + i)) := by
      unfold allBelow
      exact all_congr' fun i hi =>
        beqP (pKey ha (List.mem_range.1 hi)) (pKey hb' (List.mem_range.1 hi))
    rw [e]
    exact allN_spec (allN_spec kDist a ha) b hb
  · rw [a4_size]
    rfl
  · rw [y_size]
    rfl
  · rw [c0_size]
    rfl
  · refine allBelow_of fun i hi => ?_
    rw [beqP (pc' (pC0 hi) pr1) (pc' pr1 (pC0 hi))]
    have h := allN_spec kR1 i hi
    rwa [CFSG.KS.Raw.Orb.strictB_eq] at h
  · rw [a4E.1]
    exact a4E.2
  · rw [a4E.1]
    simp [penumRec, kCnt.2]

end CertificateChecks.KernelSpor.SuzC1EZ

end
