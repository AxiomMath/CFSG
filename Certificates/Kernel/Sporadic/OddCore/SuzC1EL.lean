module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EL0
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EL1
public import Certificates.Kernel.Sporadic.OddCore.SuzC1ER0
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP00
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP01
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP02
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP03
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP04
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP05
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP06
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP07
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP08
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP09
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP10
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP11
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP12
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP13
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP14
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP15
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP16
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP17
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP18
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP19
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP20
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP21
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP22
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EP23
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzC1EL.locAll
  CertificateChecks.KernelSpor.SuzC1EL.locS 8
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh2aAll
  CertificateChecks.KernelSpor.SuzC1EL.rh2a 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh2bAll
  CertificateChecks.KernelSpor.SuzC1EL.rh2b 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh3aAll
  CertificateChecks.KernelSpor.SuzC1EL.rh3a 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh3bAll
  CertificateChecks.KernelSpor.SuzC1EL.rh3b 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh10bAll
  CertificateChecks.KernelSpor.SuzC1EL.rh10b 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh11aAll
  CertificateChecks.KernelSpor.SuzC1EL.rh11a 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh13aAll
  CertificateChecks.KernelSpor.SuzC1EL.rh13a 32
#kon_join CertificateChecks.KernelSpor.SuzC1EL.rh14bAll
  CertificateChecks.KernelSpor.SuzC1EL.rh14b 32

namespace CertificateChecks.KernelSpor.SuzC1EL

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
local notation "pgk" => pg 11 (mask 11)

theorem kC0Inv : allN 16 c0InvK = true := by quickRfl

theorem negLoc : Bool.not (strictB (SuzC1EV.T 0) fun X => Nat.beq (pc (SuzC1ET.T 0) (c0K 1)) X) =
    true := by quickRfl

theorem kLoc {k : Nat} (hk : k < 512) : locK k = true := by
  have h := allBlk_spec (locAll (k / 64) (by exact (by omega : k / 64 < 8))) (k % 64) (Nat.mod_lt _ (by norm_num))
  change locK (64 * (k / 64) + k % 64) = true at h
  rwa [Nat.div_add_mod] at h

theorem rhoM_of_chunks {i s : Nat} (h : ∀ q < 32, rhoMK i s (16 * q) 16 = true) {m : Nat}
    (hm : m < 512) : rhoCandK (kK (wg SuzC1EWR (2 * i + s))) (SuzC1EV.T m) (c0K i)
      (pc W0 (c0K i)) = true := by
  have hq := h (m / 16) (by omega)
  unfold rhoMK at hq
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at hq
  have h' := allBlk_spec hq (m % 16) (Nat.mod_lt _ (by norm_num))
  change rhoCandK _ (SuzC1EV.T (16 * (m / 16) + m % 16)) _ _ = true at h'
  rwa [Nat.div_add_mod] at h'

theorem rhoM_of_all {i s : Nat} (h : rhoMK i s 0 512 = true) {m : Nat} (hm : m < 512) :
    rhoCandK (kK (wg SuzC1EWR (2 * i + s))) (SuzC1EV.T m) (c0K i) (pc W0 (c0K i)) = true := by
  unfold rhoMK at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at h
  have h' := allBlk_spec h m hm
  rwa [show Nat.add 0 m = m from Nat.zero_add m] at h'

theorem light : rhoMK 8 0 0 512 = true ∧ rhoMK 8 1 0 512 = true ∧ rhoMK 10 0 0 512 = true ∧
    rhoMK 11 1 0 512 = true ∧ rhoMK 13 1 0 512 = true ∧ rhoMK 14 0 0 512 = true ∧
    rhoMK 15 0 0 512 = true ∧ rhoMK 15 1 0 512 = true := by
  have h := kRhoLight
  unfold rhoLight at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem rhoM_ok {i : Nat} (hi : i ∈ rhoIs) {s : Nat} (hs : s < 2) {m : Nat} (hm : m < 512) :
    rhoCandK (kK (wg SuzC1EWR (2 * i + s))) (SuzC1EV.T m) (c0K i) (pc W0 (c0K i)) = true := by
  simp only [rhoIs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases s
  · exact rhoM_of_chunks rh2aAll hm
  · exact rhoM_of_chunks rh2bAll hm
  · exact rhoM_of_chunks rh3aAll hm
  · exact rhoM_of_chunks rh3bAll hm
  · exact rhoM_of_all light.1 hm
  · exact rhoM_of_all light.2.1 hm
  · exact rhoM_of_all light.2.2.1 hm
  · exact rhoM_of_chunks rh10bAll hm
  · exact rhoM_of_chunks rh11aAll hm
  · exact rhoM_of_all light.2.2.2.1 hm
  · exact rhoM_of_chunks rh13aAll hm
  · exact rhoM_of_all light.2.2.2.2.1 hm
  · exact rhoM_of_all light.2.2.2.2.2.1 hm
  · exact rhoM_of_chunks rh14bAll hm
  · exact rhoM_of_all light.2.2.2.2.2.2.1 hm
  · exact rhoM_of_all light.2.2.2.2.2.2.2 hm

theorem pT0k {q : Nat} (hq : q < 64) : P t0Enum.tabs[q]! (SuzC1ET.T q) :=
  ⟨t0_tabs_get hq, penumPt_canon (ptT q (by rw [kCnt.1]; exact hq))⟩

theorem pC0' {i : Nat} (hi : i < 16) : P c0Tabs[i]! (c0K i) := pC0 hi

theorem pC0I {i : Nat} (hi : i < 16) : P c0Invs[i]! (c0IK i) := by
  rw [show c0Invs[i]! = invTab 1782 c0Tabs[i]! from map_get _ (by rw [c0_size]; exact hi)]
  have h := and2 (allN_spec kC0Inv i hi)
  have h2 := and2 h.1
  exact (p_invR (pC0' hi) h2.1 h2.2).1

theorem anyBelow_of {m : Nat} {f : Nat → Bool} {i : Nat} (hi : i < m) (h : f i = true) :
    anyBelow m f = true := by
  unfold anyBelow
  rw [List.any_eq_true]
  exact ⟨i, List.mem_range.2 hi, h⟩

theorem anyBelow_arr {A : Array Tab} {f : Tab → Bool} {x : Tab} (hx : x ∈ A.toList)
    (h : f x = true) : anyBelow A.size (fun j => f A[j]!) = true := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
  have hj' : j < A.size := by simpa using hj
  refine anyBelow_of hj' ?_
  rw [getElem!_pos A j hj']
  simp only [Array.getElem_toList] at e
  rw [e]
  exact h

theorem pg_unpack {X i : Nat} (hi : i < 1782) : (unpack 1782 11 X)[i]! = pgk X i :=
  CFSG.KS.Raw.Orb.unpack_get hi

theorem locCheck_true : locCheck = true := by
  unfold locCheck
  dsimp only
  refine andT (allBelow_of fun i hi => ?_) (allBelow_of fun k hk => ?_)
  · have h := and2 (allN_spec kC0Inv i hi)
    rw [sizeP (pC0I hi), beqP (pc' (pC0I hi) (pC0' hi)) pId']
    exact andT (beq_self_eq_true _) h.2
  · have hP := pVk hk
    have h := kLoc hk
    unfold locK at h
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h
    rw [Bool.or_eq_true]
    by_cases hw : Nat.beq (wg SuzC1EWL k) 0 = true
    · right
      simp only [hw, ↓reduceIte] at h
      simp only [CFSG.KS.Raw.Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨⟨⟨⟨⟨hinv, hxi⟩, hi16⟩, hq64⟩, hJ⟩, hE⟩ := h
      have hinv' := and2 hinv
      have pXI : P (invTab 1782 v0Enum.tabs[k]!) (SuzC1EI (k + 1)) :=
        (p_invR hP hinv'.1 hinv'.2).1
      set i := Nat.mod (wg SuzC1EWM k) 16 with hi
      set q := Nat.div (wg SuzC1EWM k) 16 with hq
      refine andT (andT (andT ?_ ?_) ?_) ?_
      · rw [sizeP pXI]
        exact beq_self_eq_true _
      · rw [beqP (pc' pXI hP) pId']
        exact hxi
      · refine anyBelow_of hi16 ?_
        have pY := pc' (pc' (pc' hP (pC0' hi16)) pXI) (pC0I hi16)
        unfold isJ
        rw [beqP (pc' pY pr1) (pc' pr1 pY), beqP (pc' pY prho) (pc' prho pY)]
        exact hJ
      · have pE := pT0k hq64
        have hEE := hE
        have hmem : t0Enum.tabs[q]! ∈ t0Invols.toList := by
          unfold t0Invols
          rw [Array.toList_filter, List.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [Array.mem_toList_iff, getElem!_pos _ q (by rw [t0_size]; exact hq64)]
            exact Array.getElem_mem _
          · rw [beqP (pc' pE pE) pId']
            exact hEE.1
        refine anyBelow_arr (f := fun e => !(comp 1782 e (conjTab 1782 v0Enum.tabs[k]!
          (invTab 1782 v0Enum.tabs[k]!) e) == comp 1782 (conjTab 1782 v0Enum.tabs[k]!
          (invTab 1782 v0Enum.tabs[k]!) e) e)) hmem ?_
        have pY : P (conjTab 1782 v0Enum.tabs[k]! (invTab 1782 v0Enum.tabs[k]!) t0Enum.tabs[q]!)
            (pc (pc (SuzC1EV.T k) (SuzC1ET.T q)) (SuzC1EI (k + 1))) := by
          unfold conjTab
          exact pc' (pc' hP pE) pXI
        rw [beqP (pc' pE pY) (pc' pY pE)]
        exact hEE.2
    · left
      simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
      simp only [CFSG.KS.Raw.Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨hm, he⟩ := h
      rw [found_indexOf_iff]
      set m := Nat.sub (wg SuzC1EWL k) 1 with hmdef
      refine ⟨m, by simpa [tcTabs] using hm, ?_⟩
      have hm16 : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hd : m / 16 < 64 := by omega
      have e : tcTabs[m]! = comp 1782 t0Enum.tabs[m / 16]! c0Tabs[m % 16]! := by
        unfold tcTabs
        exact ofFn_get (fun m => comp 1782 t0Enum.tabs[m / 16]! c0Tabs[m % 16]!) hm
      rw [e, (pc' (pT0k hd) (pC0' hm16)).1, hP.1]
      exact congrArg (unpack 1782 11) (Nat.eq_of_beq_eq_true he)

theorem pre_eq {k v u y : Array Nat} {K V U Y : Nat} (hk : P k K) (hv : P v V) (hu : P u U)
    (hy : P y Y) : (allBelow 4 fun i => (comp 1782 k v)[u[i]!]! == y[(comp 1782 k v)[i]!]!) =
      preK K V U Y := by
  have hc := pc' hk hv
  unfold preK allBelow
  refine all_congr' fun i hi => ?_
  have hi' : i < 1782 := by have := List.mem_range.1 hi; omega
  have hU := pg_lt hu.2 hi'
  have hC := pg_lt hc.2 hi'
  rw [hc.1, hu.1, hy.1, pg_unpack hi', pg_unpack hU, pg_unpack hi', pg_unpack hC,
    CFSG.KS.PF.pg_pcomp (by norm_num) hU, CFSG.KS.PF.pg_pcomp (by norm_num) hi']

theorem conjEq_eq {k v u y : Array Nat} {K V U Y : Nat} (hk : P k K) (hv : P v V) (hu : P u U)
    (hy : P y Y) : conjEq (comp 1782 k v) u y = conjEqK K V (pc K V) U Y := by
  have hc := pc' hk hv
  unfold conjEq conjEqK
  rw [beqP (pc' hc hu) (pc' hy hc), pre_eq hk hv hu hy]

theorem rhoTail_eq {c : Array Nat} {C : Nat} (hc : P c C) : rhoTail c = rhoTailK C := by
  have h2 := pc' hc hc
  have h3 := pc' hc h2
  unfold rhoTail rhoTailK
  dsimp only
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, beqP (pc' h2 pw0) (pc' pw0 h2),
    beqP (pc' h3 pw0) (pc' pw0 h3), beqP h3 pId', hc.1, commT0_unpack hc.2]

theorem rhoCand_eq {k v u l : Array Nat} {K V U L : Nat} (hk : P k K) (hv : P v V)
    (hu : P u U) (hl : P l L) : rhoCand (comp 1782 k v) u l = rhoCandK K V U L := by
  unfold rhoCand rhoCandK
  rw [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.strictB_eq, conjEq_eq hk hv hu pw0,
    conjEq_eq hk hv hu hu, conjEq_eq hk hv hu hl, rhoTail_eq (pc' hk hv)]
  by_cases hp : (preK K V U W0 || preK K V U U || preK K V U L) = true
  · simp only [hp, ↓reduceIte]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    unfold conjEqK
    rw [h1, h2, h3]
    rfl

theorem rhoCond_eq {u : Array Nat} {U : Nat} (hu : P u U) :
    rhoCond (indexOf t0Enum.tabs) u = rcK U := by
  unfold rhoCond rcK
  rw [beqP (pc' hu hu) pId', (pc' pw0 hu).1, found_t0_iff (pc' pw0 hu).2, beqP hu pId',
    beqP hu pw0, hu.1, found_t0_iff hu.2]

theorem rhoCheck_true : rhoCheck = true := by
  unfold rhoCheck
  dsimp only
  refine allBelow_of fun i hi => ?_
  have hU := pC0' hi
  have hL := pc' pw0 hU
  have h := allN_spec kRhoI i hi
  have hIs := allN_spec kRcIs i hi
  unfold rhoI at h
  rw [Bool.or_eq_true] at h hIs ⊢
  by_cases hr : rcK (c0K i) = true
  · right
    have hmem : i ∈ rhoIs := by
      rcases hIs with h' | h'
      · rw [hr] at h'
        exact absurd h' (by decide)
      · simpa using h'
    have h2 : (rhoHK i 0 && rhoHK i 1) = true := by
      rcases h with h | h
      · rw [hr] at h
        exact absurd h (by decide)
      · exact h
    have hs2 := and2 h2
    refine allBelow_of fun s hs => ?_
    have hsk : rhoHK i s = true := by
      interval_cases s
      · exact hs2.1
      · exact hs2.2
    unfold rhoHK at hsk
    simp only [CFSG.KS.Raw.Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at hsk
    obtain ⟨hj, hkw⟩ := hsk
    set j := wg SuzC1EWR (2 * i + s)
    have hK : P kTabs[j]! (kK j) := by
      rw [show kTabs[j]! = kTab j from ofFn_get _ hj]
      exact pK j
    refine anyBelow_of hj (andT ?_ (allBelow_of fun m hm => ?_))
    · have hW : P (if s = 0 then c0Tabs[i]! else comp 1782 w0T c0Tabs[i]!)
          (Bool.rec (motive := fun _ => Nat) (pc W0 (c0K i)) (c0K i) (Nat.beq s 0)) := by
        interval_cases s
        · exact hU
        · exact hL
      rw [beqP (pc' hK pw0) (pc' hW hK)]
      exact hkw
    · exact (rhoCand_eq hK (pVk hm) hU hL).trans (rhoM_ok hmem hs hm)
  · left
    rw [rhoCond_eq hU]
    simpa using hr

end CertificateChecks.KernelSpor.SuzC1EL

end
