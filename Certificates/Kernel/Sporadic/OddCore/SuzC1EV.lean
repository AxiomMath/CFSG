module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV0
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV1
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV2
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV3
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV4
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV5
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV6
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV7
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV8
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV9
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVA
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzC1EV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.Sporadic.SuzRecog.C1ModelData CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1BF CertificateChecks.KernelSpor.SuzC1EG
  CertificateChecks.KernelSpor.SuzC1EF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "W0" => SuzTwG 6

theorem kHdV : penumHdK Id SuzC1EV.cnt 512 SuzC1EV.T SuzC1EV.PL = true := by quickRfl

theorem kVK {k : Nat} (hk : k < 512) : vK k = true := by
  rcases Nat.lt_or_ge k 256 with h | h
  · have := allBlk_spec kVK0 k h
    rwa [show Nat.add 0 k = k from Nat.zero_add k] at this
  · have := allBlk_spec kVK1 (k - 256) (by omega)
    rwa [show Nat.add 256 (k - 256) = k by change 256 + (k - 256) = k; omega] at this

theorem kCC' {k : Nat} (hk : k < 512) : ccK (SuzC1EV.T k) (wg SuzC1EWC k) = true := by
  have := allBlk_spec kCC k hk
  rwa [show Nat.add 0 k = k from Nat.zero_add k] at this

theorem kC0 : selFrom (fun k => Nat.beq (wg SuzC1EWC k) 0) 512 0 SuzC1EC = true := by quickRfl

theorem kC0len : SuzC1EC.length = 16 ∧ SuzC1EC.all (· < 512) = true := ⟨rfl, by quickRfl⟩

theorem negCC : Bool.not (ccK Id 1) = true := by quickRfl

theorem negSel : Bool.not (selFrom (fun k => Nat.beq (wg SuzC1EWC k) 0) 512 0 SuzC1EC.tail) =
    true := by quickRfl

theorem cover' {L N : Nat} {Q : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, L * s ≤ i → i < L * s + L → Q i) : ∀ i < L * N, Q i := by
  intro i hi
  refine h (i / L) (Nat.div_lt_of_lt_mul hi) i (Nat.mul_div_le i L) ?_
  have := Nat.lt_mul_div_succ i hL
  rw [Nat.mul_add, Nat.mul_one] at this
  exact this

theorem cntV : SuzC1EV.cnt = 512 := rfl

theorem ptV : ∀ i < SuzC1EV.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SuzC1EV.G SuzC1EV.GI
    7 SuzC1EV.cnt SuzC1EV.T SuzC1EV.PL SuzC1EV.POS SuzC1EV.SRT SuzC1EV.SRI i = true := by
  intro i hi
  have key := cover' (L := 64) (N := 8) (by norm_num) (Q := fun i => i < SuzC1EV.cnt →
      penumPtK 1782 11 (mask 11) (1782 * 11) false SuzC1EV.G SuzC1EV.GI 7 SuzC1EV.cnt SuzC1EV.T
        SuzC1EV.PL SuzC1EV.POS SuzC1EV.SRT SuzC1EV.SRI i = true)
    (fun s hs i h1 h2 hc => by
      have hsl : slV s = true := by
        interval_cases s
        exacts [slV0, slV1, slV2, slV3, slV4, slV5, slV6, slV7]
      exact penumSl_spec hsl i h1 h2 hc)
  exact key i (by rw [cntV] at hi; omega) hi

theorem v0E : v0Enum = penumRec 1782 11 SuzC1EV.cnt SuzC1EV.T SuzC1EV.PL ∧
    enumOK 1782 v0Tabs (penumRec 1782 11 SuzC1EV.cnt SuzC1EV.T SuzC1EV.PL) = true :=
  penumK_left_sound kSz gV0 kHdV ptV

theorem canV {k : Nat} (hk : k < 512) : cn (SuzC1EV.T k) = true :=
  penumPt_canon (ptV k (by rw [cntV]; exact hk))

theorem pVk {k : Nat} (hk : k < 512) : P v0Enum.tabs[k]! (SuzC1EV.T k) := by
  refine ⟨?_, canV hk⟩
  rw [v0E.1]
  exact ofFn_get (fun i => unpack 1782 11 (SuzC1EV.T i)) (by rw [cntV]; exact hk)

theorem v0_size : v0Enum.tabs.size = 512 := by
  rw [v0E.1]
  simp [penumRec, cntV]

theorem memT_iff {X : Nat} : memT X = true ↔ ∃ q < 64, SuzC1ET.T q = X := by
  refine ⟨memT_spec, fun ⟨q, hq, e⟩ => ?_⟩
  unfold memT
  cases h : allN 64 (fun q => !Nat.beq (SuzC1ET.T q) X)
  · rfl
  · have := allN_spec h q hq
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem found_t0_iff {X : Nat} (hX : cn X = true) :
    found (indexOf t0Enum.tabs) t0Enum.tabs (unpack 1782 11 X) = memT X := by
  cases h : memT X
  · cases h' : found (indexOf t0Enum.tabs) t0Enum.tabs (unpack 1782 11 X)
    · rfl
    · rw [t0E.1] at h'
      obtain ⟨q, hq, e⟩ := (found_penumRec_iff ptT hX).1 h'
      rw [memT_iff.2 ⟨q, by rw [kCnt.1] at hq; exact hq, e⟩] at h
      exact absurd h (by decide)
  · exact found_t0 h

theorem fixedCount_eq' {X : Nat} : fixedCount (unpack 1782 11 X) = fixCntK 1782 11 (mask 11) X :=
  OddCore.fixedCount_unpack

theorem v0Check_true : v0Check = true := by
  unfold v0Check
  refine andT (andT ?_ ?_) (allBelow_of fun k hk => ?_)
  · rw [v0E.1]
    exact v0E.2
  · rw [v0_size]
    rfl
  · have hP := pVk hk
    have h := kVK hk
    unfold vK at h
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h
    rw [beqP (pc' hP hP) pId', beqP hP pId', hP.1, fixedCount_eq', found_t0_iff hP.2]
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (beq_iff_eq.2 (Nat.eq_of_beq_eq_true h)))
    · exact Or.inr h

theorem commT0_unpack {X : Nat} (hX : cn X = true) : commT0 (unpack 1782 11 X) = cK X := by
  unfold commT0 cK allBelow
  refine all_congr' fun i hi => ?_
  have hi' : i < 4 := List.mem_range.1 hi
  have hP : P (unpack 1782 11 X) X := ⟨rfl, hX⟩
  exact beqP (pc' hP (pT0 hi')) (pc' (pT0 hi') hP)

theorem pg_lt {X i : Nat} (hX : cn X = true) (hi : i < 1782) : pg 11 (mask 11) X i < 1782 :=
  (CFSG.KS.PF.canon_facts hX).2.2.2 i hi

theorem ccK_spec {X c : Nat} (hX : cn X = true) (h : ccK X c = true) :
    commT0 (unpack 1782 11 X) = Nat.beq c 0 := by
  rw [commT0_unpack hX]
  unfold ccK at h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  by_cases hc : Nat.beq c 0 = true
  · rw [hc] at h ⊢
    exact h
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, CFSG.KS.Raw.Orb.strictB_eq,
      CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    obtain ⟨hj, hp, hne⟩ := h
    have hj : (c - 1) / 2048 < 4 := hj
    have hp : (c - 1) % 2048 < 1782 := hp
    have hne : Nat.beq (pg 11 (mask 11) X (pg 11 (mask 11) (SuzC1ET.G ((c - 1) / 2048))
        ((c - 1) % 2048))) (pg 11 (mask 11) (SuzC1ET.G ((c - 1) / 2048))
        (pg 11 (mask 11) X ((c - 1) % 2048))) = false := hne
    rw [Bool.eq_false_iff.2 hc]
    unfold cK allBelow
    rw [Bool.eq_false_iff, Ne, List.all_eq_true, not_forall]
    refine ⟨(c - 1) / 2048, fun hall => ?_⟩
    have hb := hall (List.mem_range.2 hj)
    have e := Nat.eq_of_beq_eq_true hb
    have hG := (pT0 hj).2
    have e2 : pg 11 (mask 11) (pc X (SuzC1ET.G ((c - 1) / 2048))) ((c - 1) % 2048) =
        pg 11 (mask 11) (pc (SuzC1ET.G ((c - 1) / 2048)) X) ((c - 1) % 2048) := by rw [e]
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) hp, CFSG.KS.PF.pg_pcomp (by norm_num) hp] at e2
    rw [e2, Nat.beq_refl] at hne
    exact absurd hne (by decide)

theorem v0_filter : (List.range 512).filter (fun k => commT0 (unpack 1782 11 (SuzC1EV.T k))) =
    SuzC1EC := by
  rw [← sel_spec kC0]
  apply List.filter_congr
  intro k hk
  have hk' := List.mem_range.1 hk
  exact ccK_spec (canV hk') (kCC' hk')

theorem c0Tabs_eq : c0Tabs = (SuzC1EC.map fun k => unpack 1782 11 (SuzC1EV.T k)).toArray := by
  unfold c0Tabs
  rw [v0E.1, penumRec_eq]
  simp only
  rw [cntV, filter_ofFn 512 (fun i => unpack 1782 11 (SuzC1EV.T i)), v0_filter]

theorem c0_size : c0Tabs.size = 16 := by
  rw [c0Tabs_eq]
  simp [kC0len.1]

theorem c0_lt {i : Nat} (hi : i < 16) : SuzC1EC.getD i 0 < 512 := by
  have h := kC0len.2
  rw [List.all_eq_true] at h
  have hi' : i < SuzC1EC.length := by rw [kC0len.1]; exact hi
  rw [List.getD_eq_getElem _ _ hi']
  simpa using h _ (List.getElem_mem hi')

theorem c0Tabs_get {i : Nat} (hi : i < 16) :
    c0Tabs[i]! = unpack 1782 11 (SuzC1EV.T (SuzC1EC.getD i 0)) := by
  have hi' : i < SuzC1EC.length := by rw [kC0len.1]; exact hi
  rw [c0Tabs_eq, getElem!_pos _ i (by simpa using hi'), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

theorem pC0 {i : Nat} (hi : i < 16) : P c0Tabs[i]! (SuzC1EV.T (SuzC1EC.getD i 0)) :=
  ⟨c0Tabs_get hi, canV (c0_lt hi)⟩

end CertificateChecks.KernelSpor.SuzC1EV

end
