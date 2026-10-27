module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EG
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzC1EF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.Sporadic.SuzRecog.C1ModelData CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1BF CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "W0" => SuzTwG 6
local notation "T1" => SuzInvT1.F 0

@[expose] noncomputable def memT (X : Nat) : Bool := !allN 64 (fun q => !Nat.beq (SuzC1ET.T q) X)

theorem kHdT : penumHdK Id SuzC1ET.cnt 64 SuzC1ET.T SuzC1ET.PL = true := by quickRfl

theorem kSlT : penumSlK 1782 11 (mask 11) (1782 * 11) false SuzC1ET.G SuzC1ET.GI 4 SuzC1ET.cnt
    SuzC1ET.T SuzC1ET.PL SuzC1ET.POS SuzC1ET.SRT SuzC1ET.SRI 0 64 = true := by quickRfl

theorem kHdB : penumHdK SuzC1EB.R SuzC1EB.cnt 3 SuzC1EB.T SuzC1EB.PL = true := by quickRfl

theorem kSlB : penumSlK 1782 11 (mask 11) (1782 * 11) true SuzC1EB.G SuzC1EB.GI 7 SuzC1EB.cnt
    SuzC1EB.T SuzC1EB.PL SuzC1EB.POS SuzC1EB.SRT SuzC1EB.SRI 0 3 = true := by quickRfl

theorem kHdN : penumHdK SuzC1EN.R SuzC1EN.cnt 24 SuzC1EN.T SuzC1EN.PL = true := by quickRfl

theorem kSlN : penumSlK 1782 11 (mask 11) (1782 * 11) true SuzC1EN.G SuzC1EN.GI 11 SuzC1EN.cnt
    SuzC1EN.T SuzC1EN.PL SuzC1EN.POS SuzC1EN.SRT SuzC1EN.SRI 0 24 = true := by quickRfl

theorem kCnt : SuzC1ET.cnt = 64 ∧ SuzC1EB.cnt = 3 ∧ SuzC1EN.cnt = 24 := ⟨rfl, rfl, rfl⟩

theorem kComT : allN 4 (fun i => Nat.beq (pc (SuzC1ET.G i) W0) (pc W0 (SuzC1ET.G i)) &&
    Nat.beq (pc (SuzC1ET.G i) (SuzC1BT 11)) (pc (SuzC1BT 11) (SuzC1ET.G i)) &&
    Nat.beq (pc (SuzC1ET.G i) (SuzTwG 2)) (pc (SuzTwG 2) (SuzC1ET.G i))) = true := by quickRfl

theorem kConjT : allN 4 (fun i => Nat.beq (pc (wK tzK (t0ConjWords.getD i [])) T1)
    (pc (SuzC1ET.G i) (wK tzK (t0ConjWords.getD i [])))) = true := by quickRfl

theorem kE3 : (Nat.beq (pc (SuzC1EI 0) e3xK) Id && memT e3K) = true := by quickRfl

theorem kInvB : allN 7 (fun k => Nat.beq (pc (SuzC1EB.GI k) (SuzC1EB.G k)) Id) = true := by
  quickRfl

theorem kInvN : allN 11 (fun k => Nat.beq (pc (SuzC1EN.GI k) (SuzC1EN.G k)) Id) = true := by
  quickRfl

theorem kNorm : allN 11 (fun j => allN 4 fun i =>
    memT (pc (pc (SuzC1EN.G j) (SuzC1ET.G i)) (SuzC1EN.GI j)) &&
    memT (pc (pc (SuzC1EN.GI j) (SuzC1ET.G i)) (SuzC1EN.G j))) = true := by quickRfl

theorem negSlT : Bool.not (penumSlK 1782 11 (mask 11) (1782 * 11) false SuzC1ET.G SuzC1ET.GI 4
    SuzC1ET.cnt (fun i => if i = 5 then Nat.xor (SuzC1ET.T i) 2 else SuzC1ET.T i) SuzC1ET.PL
    SuzC1ET.POS SuzC1ET.SRT SuzC1ET.SRI 0 64) = true := by quickRfl

theorem negMem : Bool.not (memT W0) = true := by quickRfl

theorem ptT : ∀ i < SuzC1ET.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false SuzC1ET.G SuzC1ET.GI
    4 SuzC1ET.cnt SuzC1ET.T SuzC1ET.PL SuzC1ET.POS SuzC1ET.SRT SuzC1ET.SRI i = true :=
  fun i hi => penumSl_spec kSlT i (Nat.zero_le _) (by rw [kCnt.1] at hi; omega) hi

theorem t0E : t0Enum = penumRec 1782 11 SuzC1ET.cnt SuzC1ET.T SuzC1ET.PL ∧
    enumOK 1782 t0Tabs (penumRec 1782 11 SuzC1ET.cnt SuzC1ET.T SuzC1ET.PL) = true :=
  penumK_left_sound kSz gT0 kHdT ptT

theorem t0_tabs_get {i : Nat} (hi : i < 64) : t0Enum.tabs[i]! = unpack 1782 11 (SuzC1ET.T i) := by
  rw [t0E.1]
  exact ofFn_get (fun i => unpack 1782 11 (SuzC1ET.T i)) (by rw [kCnt.1]; exact hi)

theorem t0_size : t0Enum.tabs.size = 64 := by
  rw [t0E.1]
  simp [penumRec, kCnt.1]

theorem memT_spec {X : Nat} (h : memT X = true) : ∃ q < 64, SuzC1ET.T q = X := by
  unfold memT at h
  by_contra hn
  have : allN 64 (fun q => !Nat.beq (SuzC1ET.T q) X) = true := by
    refine CFSG.KS.PEnum.allN_of fun q hq => ?_
    have hne : SuzC1ET.T q ≠ X := fun e => hn ⟨q, hq, e⟩
    simp [beq_false hne]
  rw [this] at h
  exact absurd h (by decide)

theorem found_t0 {X : Nat} (h : memT X = true) :
    found (indexOf t0Enum.tabs) t0Enum.tabs (unpack 1782 11 X) = true := by
  obtain ⟨q, hq, e⟩ := memT_spec h
  rw [t0E.1]
  exact penum_found_sound ptT (by rw [kCnt.1]; exact hq) e

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem t0Check_true : t0Check = true := by
  unfold t0Check
  refine andT (andT (andT (andT (andT (andT ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · rw [t0E.1]
    exact t0E.2
  · rw [t0_size]
    rfl
  · refine allBelow_of fun i hi => ?_
    rw [beqP (pc' (pT0 hi) pw0) (pc' pw0 (pT0 hi)), beqP (pc' (pT0 hi) pr1) (pc' pr1 (pT0 hi)),
      beqP (pc' (pT0 hi) prho) (pc' prho (pT0 hi))]
    exact allN_spec kComT i hi
  · refine allBelow_of fun i hi => ?_
    rw [beqP (pc' (pConj i) pt1) (pc' (pT0 hi) (pConj i))]
    exact allN_spec kConjT i hi
  · rw [sizeP pe3xI]
    rfl
  · rw [beqP (pc' pe3xI pe3x) pId']
    exact (and2 kE3).1
  · rw [pe3.1]
    exact found_t0 (and2 kE3).2

theorem invsOK_of {gens ginv : Array Tab} {G GI : Nat → Nat} {k : Nat}
    (hs : gens.size = k) (hsi : ginv.size = k) (hg : ∀ j < k, P gens[j]! (G j))
    (hgi : ∀ j < k, P ginv[j]! (GI j)) (h : allN k (fun j => Nat.beq (pc (GI j) (G j)) Id) = true) :
    invsOK 1782 gens ginv = true := by
  unfold invsOK
  refine andT (by rw [hs, hsi]; exact beq_self_eq_true k) (allBelow_of fun j hj => ?_)
  rw [hs] at hj
  refine andT ?_ ?_
  · rw [sizeP (hgi j hj)]
    rfl
  · rw [beqP (pc' (hgi j hj) (hg j hj)) pId']
    exact allN_spec h j hj

theorem pR {X : Nat} (hX : X = W0) : w0T = unpack 1782 11 X := by
  rw [hX]
  exact pw0.1

theorem ptB : ∀ i < SuzC1EB.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SuzC1EB.G SuzC1EB.GI
    7 SuzC1EB.cnt SuzC1EB.T SuzC1EB.PL SuzC1EB.POS SuzC1EB.SRT SuzC1EB.SRI i = true :=
  fun i hi => penumSl_spec kSlB i (Nat.zero_le _) (by rw [kCnt.2.1] at hi; omega) hi

theorem ptN : ∀ i < SuzC1EN.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) true SuzC1EN.G SuzC1EN.GI
    11 SuzC1EN.cnt SuzC1EN.T SuzC1EN.PL SuzC1EN.POS SuzC1EN.SRT SuzC1EN.SRI i = true :=
  fun i hi => penumSl_spec kSlN i (Nat.zero_le _) (by rw [kCnt.2.2] at hi; omega) hi

theorem normCheck_true : normCheck = true := by
  have hR := and2 kBR
  have hB := penumK_conj_sound kSz gB0 gB0I (pR (Nat.eq_of_beq_eq_true hR.1)) kHdB ptB
  have hN := penumK_conj_sound kSz gNT0 gNT0I (pR (Nat.eq_of_beq_eq_true hR.2)) kHdN ptN
  have iB : invsOK 1782 b0Tabs b0Invs = true :=
    invsOK_of (by simp [b0Tabs]) (by simp [b0Invs, b0Tabs]) (fun _ hj => pB0 hj)
      (fun _ hj => pB0I hj) kInvB
  have iN : invsOK 1782 nt0Tabs nt0Invs = true :=
    invsOK_of (by simp [nt0Tabs]) (by simp [nt0Invs, nt0Tabs]) (fun _ hj => pNT0 hj)
      (fun _ hj => pNT0I hj) kInvN
  have hsB : b0Tabs.size = 7 := by simp [b0Tabs]
  have hsN : nt0Tabs.size = 11 := by simp [nt0Tabs]
  have hsT : t0Tabs.size = 4 := by simp [t0Tabs]
  unfold normCheck orbitOK b0Orbit nt0Orbit
  rw [hB.1, hN.1, iB, iN, hB.2, hN.2]
  refine andT (andT (andT (andT rfl ?_) ?_) rfl) ?_
  · simp [penumRec, kCnt.2.1]
  · unfold normalOK
    refine andT iN (allBelow_of fun j hj => allBelow_of fun i hi => ?_)
    rw [hsN] at hj
    rw [hsT] at hi
    have h := and2 (allN_spec (allN_spec kNorm j hj) i hi)
    unfold conjTab
    refine andT ?_ ?_
    · rw [(pc' (pc' (pNT0 hj) (pT0 hi)) (pNT0I hj)).1]
      exact found_t0 h.1
    · rw [(pc' (pc' (pNT0I hj) (pT0 hi)) (pNT0 hj)).1]
      exact found_t0 h.2
  · simp [penumRec, kCnt.2.2]

end CertificateChecks.KernelSpor.SuzC1EF

end
