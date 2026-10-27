module

public import Certificates.Kernel.Sporadic.OddCore.SuzRgC
public import Certificates.Kernel.Sporadic.OddCore.SuzFb
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.HeFixKFix
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzRg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.RigidL2 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "g7" => pg 7 (mask 7)
local notation "cn7" => canonK 64 7 (mask 7) (64 * 7)
local notation "W" => SuzFb.W
local notation "QE" => KernelLC.SuzB0QE
local notation "nget" => CFSG.KS.Mathieu.nget

theorem not_t {a : Bool} (h : Bool.not a = true) : a = false := by
  cases a <;> simp_all

theorem and_t {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := (bAnd_iff a b).1 h

theorem g1 {a : Array Nat} {A : Nat} (ha : P a A) {z : Nat} (hz : z < 1782) : a[z]! = pgk A z :=
  SuzFb.get_P ha hz

theorem l1 {a : Array Nat} {A : Nat} (ha : P a A) {z : Nat} (hz : z < 1782) : pgk A z < 1782 :=
  SuzFb.pgl ha.2 hz

theorem g2 {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) {z : Nat} (hz : z < 1782) :
    a[b[z]!]! = pgk A (pgk B z) := by
  rw [g1 hb hz, g1 ha (l1 hb hz)]

theorem g3 {a b d : Array Nat} {A B D : Nat} (ha : P a A) (hb : P b B) (hd : P d D) {z : Nat}
    (hz : z < 1782) : a[b[d[z]!]!]! = pgk A (pgk B (pgk D z)) := by
  rw [g1 hd hz, g2 ha hb (l1 hd hz)]

theorem pQ {i : Nat} (hi : i < 128) : P qElts[i]! (QE i) := SuzFb.pQE hi

theorem comm_P {x y : Array Nat} {X Y : Nat} (hx : P x X) (hy : P y Y) :
    rigComm x y = Nat.beq (pc X Y) (pc Y X) := by
  rw [← eqA_P (p_comp hx hy) (p_comp hy hx)]
  unfold rigComm eqA
  refine SuzFb.allLt_congr' fun z hz => ?_
  rw [CFSG.Monster.B.Co2.compA_get hz, CFSG.Monster.B.Co2.compA_get hz]

theorem comm_false {x y : Array Nat} {X Y : Nat} (hx : P x X) (hy : P y Y) {p : Nat}
    (hp : p < 1782) (h : Nat.beq (pgk X (pgk Y p)) (pgk Y (pgk X p)) = false) :
    rigComm x y = false := by
  refine Bool.eq_false_iff.2 fun hc => ?_
  have := CFSG.Monster.B.Co2.allLt_spec hc hp
  rw [g2 hx hy hp, g2 hy hx hp, SuzFb.beqN, h] at this
  exact absurd this (by decide)

theorem commV_true {x y : Array Nat} {X Y : Nat} (hx : P x X) (hy : P y Y) {i : Nat} (hi : i < 4)
    (h : Nat.beq (pc X Y) (pc (QE i) (pc Y X)) = true) : rigCommV x y = true := by
  unfold rigCommV anyBelow
  refine List.any_eq_true.2 ⟨i, List.mem_range.2 hi, ?_⟩
  have e := eqA_P (p_comp hx hy) (p_comp (pQ (by omega : i < 128)) (p_comp hy hx))
  rw [h] at e
  unfold eqA at e
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun z hz => ?_
  have := CFSG.Monster.B.Co2.allLt_spec e hz
  rwa [CFSG.Monster.B.Co2.compA_get hz, CFSG.Monster.B.Co2.compA_get hz,
    CFSG.Monster.B.Co2.compA_get hz] at this

theorem commV_false {x y : Array Nat} {X Y : Nat} (hx : P x X) (hy : P y Y)
    (h : ∀ i < 4, ∃ z < 1782, Nat.beq (pgk X (pgk Y z)) (pgk (QE i) (pgk Y (pgk X z))) = false) :
    rigCommV x y = false := by
  unfold rigCommV anyBelow
  rw [List.any_eq_false]
  intro i hi hc
  have hi4 := List.mem_range.1 hi
  obtain ⟨z, hz, hne⟩ := h i hi4
  have := CFSG.Monster.B.Co2.allLt_spec hc hz
  rw [g2 hx hy hz, g2 hy hx hz, g1 (pQ (by omega : i < 128)) (l1 hy (l1 hx hz)), SuzFb.beqN,
    hne] at this
  exact absurd this (by decide)

theorem eqComp_P {x p q : Array Nat} {X Pk Q : Nat} (hx : P x X) (hp : P p Pk) (hq : P q Q) :
    rigEqComp x p q = Nat.beq X (pc Pk Q) := by
  rw [← eqA_P hx (p_comp hp hq)]
  unfold rigEqComp eqA
  refine SuzFb.allLt_congr' fun y hy => ?_
  rw [CFSG.Monster.B.Co2.compA_get hy]

theorem all2 {f : Nat → Nat → Bool} (h : ∀ c < 16, ∀ j < 128, f c j = true) :
    ((List.range 16).all fun c => allLt 128 fun j => f c j) = true := by
  rw [List.all_eq_true]
  intro c hc
  exact CFSG.Monster.B.Co2.allLt_iff.2 (h c (List.mem_range.1 hc))

theorem ofFn2 {α : Type} [Inhabited α] {n m : Nat} (f : Nat → Nat → α) {i j : Nat} (hi : i < n)
    (hj : j < m) :
    ((Array.ofFn (n := n) fun a => Array.ofFn (n := m) fun b => f a.val b.val)[i]!)[j]! =
      f i j := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem blk {L : Nat} {f : Nat → Bool} {s : Nat} (h : allBlk (Nat.mul L s) f L = true) {i : Nat}
    (h1 : L * s ≤ i) (h2 : i < L * s + L) : f i = true := by
  have := allBlk_spec h (i - L * s) (by omega)
  have e : Nat.add (Nat.mul L s) (i - L * s) = i := by
    change L * s + (i - L * s) = i
    omega
  rwa [e] at this

theorem kU' {c : Nat} (hc : c < 16) : (∀ k ∈ rigUWords.getD c [], k < 10) ∧
    Nat.beq (SuzRgU c) (utK c) = true := by
  obtain ⟨h1, h2⟩ := and_t (allN_spec kU c hc)
  exact ⟨SuzFb.letters h1, h2⟩

theorem pU {c : Nat} (hc : c < 16) : P (rigUTab c) (SuzRgU c) := by
  obtain ⟨hw, hb⟩ := kU' hc
  refine p_eq ?_ hb
  have hW := cWord_P _ hw
  have e2 : qProds[2]! = qProd 2 := by
    unfold qProds
    rw [getElem!_pos _ 2 (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
  unfold rigUTab utK
  rw [SuzFb.beqN]
  cases hf : Nat.beq (rigUFix.getD c 0) 1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hW
  · simp only [↓reduceIte]
    rw [e2]
    exact p_comp (pqProd 2) hW

theorem rtab_eq {c j : Nat} (hc : c < 16) (hj : j < 128) :
    rigRTab c j = compA 1782 (rigUTab c) qElts[j]! := by
  unfold rigRTab rigRTabs
  exact ofFn2 (fun c j => compA 1782 (rigUTab c) qElts[j]!) hc hj

theorem pR {c j : Nat} (hc : c < 16) (hj : j < 128) :
    P (rigRTab c j) (pc (SuzRgU c) (QE j)) := by
  rw [rtab_eq hc hj]
  exact p_comp (pU hc) (pQ hj)

theorem kT' {i : Nat} (hi : i < 8) : (gen i).2.2.1 < 16 ∧ (gen i).2.2.2 < 128 ∧
    Nat.beq (SuzRgT i) (pc (SuzRgU (gen i).2.2.1) (QE (gen i).2.2.2)) = true := by
  obtain ⟨h1, h2⟩ := and_t (allN_spec kT i hi)
  obtain ⟨h3, h4⟩ := and_t h2
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h3, h4⟩

theorem ttab_eq (i : Nat) : rigTTab i = rigRTab (gen i).2.2.1 (gen i).2.2.2 := rfl

theorem pT {i : Nat} (hi : i < 8) : P (rigTTab i) (SuzRgT i) := by
  obtain ⟨h1, h2, h3⟩ := kT' hi
  rw [ttab_eq]
  exact p_eq (pR h1 h2) h3

theorem stab_eq (s : Nat) :
    rigSTab s = rigRTab (rigSeeds.getD s (0, 0)).1 (rigSeeds.getD s (0, 0)).2 := by
  unfold rigSTab
  generalize rigSeeds.getD s (0, 0) = t
  obtain ⟨a, b⟩ := t
  rfl

theorem pSK {s : Nat} (hs : s < 2) : P (rigSTab s) (SK s) := by
  rw [stab_eq]
  interval_cases s
  · have e1 : rigSeeds.getD 0 (0, 0) = (0, 24) := rfl
    have e2 : gen 0 = (0, [], 0, 24) := rfl
    have h := pT (i := 0) (by norm_num)
    rw [ttab_eq, e2] at h
    rw [e1]
    exact h
  · have e1 : rigSeeds.getD 1 (0, 0) = (6, 0) := rfl
    have e2 : gen 4 = (1, [], 6, 0) := rfl
    have h := pT (i := 4) (by norm_num)
    rw [ttab_eq, e2] at h
    rw [e1]
    exact h

theorem pV0 : P (cWord rigX1) (SuzRgV 0) := p_eq (cWord_P _ (by decide)) kV0

theorem pSS {s : Nat} (hs : s < 2) :
    P (compA 1782 (rigSTab s) (rigSTab s)) (SuzRgV (Nat.add 1 s)) :=
  p_eq (p_comp (pSK hs) (pSK hs)) (allN_spec kVS s hs)

theorem seed_facts {s : Nat} (hs : s < 2) : seedK s = true ∧ ∀ g < 2, gamK s g = true := by
  obtain ⟨h1, h2⟩ := and_t (allN_spec kSeed s hs)
  exact ⟨h1, fun g hg => allN_spec h2 g hg⟩

theorem gam_facts {s g : Nat} (hs : s < 2) (hg : g < 2) : (∀ k ∈ gam s g, k < 10) ∧
    Nat.beq (pc (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g))) W)
      (pc W (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g)))) = true ∧
    ∃ i < 4, Nat.beq (pc (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g))) (SK s))
      (pc (QE i) (pc (SK s) (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g))))) = true := by
  have h := (seed_facts hs).2 g hg
  unfold gamK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  obtain ⟨h1, h2⟩ := and_t h
  obtain ⟨h3, h4⟩ := and_t h2
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h4
  obtain ⟨h5, h6⟩ := and_t h4
  exact ⟨SuzFb.letters h1, h3, _, Nat.blt_eq.mp h5, h6⟩

theorem pG {s g : Nat} (hs : s < 2) (hg : g < 2) :
    P (cWord (gam s g)) (SuzRgV (Nat.add 3 (Nat.add (Nat.mul 2 s) g))) :=
  p_eq (cWord_P _ (gam_facts hs hg).1) (allN_spec (allN_spec kVG s hs) g hg)

theorem pPT {m : Nat} (hm : m < 256) : P rigProdTabs[m]! (SuzRgPT m) := by
  have hb : Nat.beq (SuzRgPT m) (ptK m) = true := by
    have hs : m / 16 < 16 := by omega
    have h := ptSlAll (m / 16) hs
    unfold ptSl at h
    exact blk h (by omega) (by omega)
  refine p_eq ?_ hb
  have key : ∀ l : List Nat, (∀ i ∈ l, i < 8) → ∀ r R, P r R →
      P (l.foldl (fun acc i => if m.testBit i then compA 1782 acc (rigTTab i) else acc) r)
        (l.foldl (fun acc i => if m.testBit i then pc acc (SuzRgT i) else acc) R) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ h => h
    | cons a l ih =>
      intro hl r R h
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ _ ?_
      by_cases hb : m.testBit a = true
      · simp only [hb, ↓reduceIte]
        exact p_comp h (pT (hl a List.mem_cons_self))
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact h
  have e : rigProdTabs[m]! = (List.range 8).foldl
      (fun acc i => if m.testBit i then compA 1782 acc (rigTTab i) else acc) (idA 1782) := by
    unfold rigProdTabs
    exact ofFn_get (fun m => (List.range 8).foldl
      (fun acc i => if m.testBit i then compA 1782 acc (rigTTab i) else acc) (idA 1782)) hm
  rw [e]
  exact key _ (fun i hi => List.mem_range.1 hi) _ _ pidn_P

theorem ncv4_spec {X Y F b : Nat} (h : ncv4 X Y F b = true) :
    ∀ i < 4, ∃ z < 1782, Nat.beq (pgk X (pgk Y z)) (pgk (QE i) (pgk Y (pgk X z))) = false := by
  unfold ncv4 at h
  obtain ⟨h0, h⟩ := and_t h
  obtain ⟨h1, h⟩ := and_t h
  obtain ⟨h2, h3⟩ := and_t h
  have sp : ∀ {i z}, ncvAt X Y i z = true →
      ∃ z < 1782, Nat.beq (pgk X (pgk Y z)) (pgk (QE i) (pgk Y (pgk X z))) = false := by
    intro i z hz
    unfold ncvAt at hz
    obtain ⟨a, b⟩ := and_t hz
    exact ⟨z, Nat.blt_eq.mp a, not_t b⟩
  intro i hi
  interval_cases i
  exacts [sp h0, sp h1, sp h2, sp h3]

theorem cellK_of {c j : Nat} (hc : c < 16) (hj : j < 128) : cellK c j = true := by
  have hs : 8 * c + j / 16 < 128 := by omega
  have h := cellSlAll (8 * c + j / 16) hs
  unfold cellSl at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  have e1 : Nat.shiftRight (8 * c + j / 16) 3 = c := by
    change (8 * c + j / 16) >>> 3 = c
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (8 * c + j / 16) 7 = j / 16 := by
    change (8 * c + j / 16) &&& (2 ^ 3 - 1) = j / 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [e1, e2] at h
  exact blk h (by omega) (by omega)

@[expose] def decB (c j : Nat) : Bool := !(rigComm (rigRTab c j) w0Tab) ||
  anyBelow 256 fun m => anyBelow 4 fun i => rigEqComp (rigRTab c j) rigProdTabs[m]! qElts[i]!

@[expose] def cenB (c j : Nat) : Bool := !(rigComm (rigRTab c j) w0Tab) ||
  !((List.range 8).all fun i => rigComm (rigRTab c j) (rigTTab i)) || (c == 0 && j < 4)

@[expose] def x1B (c j : Nat) : Bool := !(rigComm (rigRTab c j) w0Tab) ||
  !(rigCommV (rigRTab c j) (cWord rigX1)) || (c == 0 && j < 4)

@[expose] def stB (s c j : Nat) : Bool := !(rigComm (rigRTab c j) w0Tab) ||
  !((rigGam.getD s []).all fun g => rigCommV (cWord g) (rigRTab c j)) ||
  !(eqA 1782 (compA 1782 (rigRTab c j) (rigRTab c j)) (compA 1782 (rigSTab s) (rigSTab s))) ||
  rigModV (rigRTab c j) (rigSTab s)

theorem nc_U {c j p : Nat} (hc : c < 16) (hj : j < 128) (hp : p < 1782)
    (h : Nat.beq (pgk (SuzRgU c) (pgk (QE j) (pgk W p)))
      (pgk W (pgk (SuzRgU c) (pgk (QE j) p))) = false) :
    rigComm (rigRTab c j) w0Tab = false := by
  have hu := pU hc
  have hq := pQ hj
  rw [rtab_eq hc hj]
  refine Bool.eq_false_iff.2 fun hc' => ?_
  have := CFSG.Monster.B.Co2.allLt_spec hc' hp
  rw [CFSG.Monster.B.Co2.compA_get (SuzFb.lt_of_P SuzFb.pW hp), CFSG.Monster.B.Co2.compA_get hp,
    g3 hu hq SuzFb.pW hp, g3 SuzFb.pW hu hq hp, SuzFb.beqN, h] at this
  exact absurd this (by decide)

theorem inV_iff {c j : Nat} : inV c j = (c == 0 && j < 4) := by
  unfold inV
  rw [CFSG.KS.Raw.Orb.bAnd_eq, SuzFb.beqN]
  congr 1

theorem st_ok {s c j RK F : Nat} (hs : s < 2) (hR : P (rigRTab c j) RK)
    (h : stK s RK F = true) : stB s c j = true := by
  unfold stK at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at h
  generalize Nat.add 9 (Nat.mul 6 s) = b at h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  unfold stB
  split_ifs at h with h1
  · obtain ⟨ha, hn⟩ := and_t h
    have hz := Nat.blt_eq.mp ha
    have hf : eqA 1782 (compA 1782 (rigRTab c j) (rigRTab c j))
        (compA 1782 (rigSTab s) (rigSTab s)) = false := by
      refine Bool.eq_false_iff.2 fun he => ?_
      have := CFSG.Monster.B.Co2.allLt_spec he hz
      rw [CFSG.Monster.B.Co2.compA_get hz, CFSG.Monster.B.Co2.compA_get hz, g2 hR hR hz,
        ← CFSG.Monster.B.Co2.compA_get hz, g1 (pSS hs) hz, SuzFb.beqN, not_t hn] at this
      exact absurd this (by decide)
    rw [hf]
    simp
  · rw [CFSG.KS.Raw.Orb.bIf_eq] at h
    split_ifs at h with h2
    · obtain ⟨ha, hn⟩ := and_t h
      generalize fl F (Nat.add b 1) = a at ha hn
      have ha' := Nat.blt_eq.mp ha
      have hf := commV_false (pG hs ha') hR (ncv4_spec hn)
      have hmem : gam s a ∈ rigGam.getD s [] := by
        interval_cases s <;> interval_cases a <;> decide
      have hall : ((rigGam.getD s []).all fun g => rigCommV (cWord g) (rigRTab c j)) = false :=
        List.all_eq_false.2 ⟨_, hmem, by simp [hf]⟩
      rw [hall]
      simp
    · obtain ⟨ha, hn⟩ := and_t h
      have ha' := Nat.blt_eq.mp ha
      have hm : rigModV (rigRTab c j) (rigSTab s) = true := by
        unfold rigModV anyBelow
        refine List.any_eq_true.2 ⟨_, List.mem_range.2 ha', ?_⟩
        rw [eqComp_P hR (pSK hs) (pQ (by omega)), hn]
      rw [hm]
      simp

theorem cell_facts {c j : Nat} (hc : c < 16) (hj : j < 128) : decB c j = true ∧ cenB c j = true ∧
    x1B c j = true ∧ stB 0 c j = true ∧ stB 1 c j = true := by
  have hK := cellK_of hc hj
  unfold cellK at hK
  rw [CFSG.KS.Raw.Orb.strictB_eq] at hK
  generalize pg 256 (mask 256) (SuzRgE c) j = F at hK
  unfold cellR at hK
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at hK
  have hR := pR hc hj
  split_ifs at hK with h0
  · obtain ⟨h1, h2⟩ := and_t hK
    have hn := nc_U hc hj (Nat.blt_eq.mp h1) (not_t h2)
    unfold decB cenB x1B stB
    simp only [hn, Bool.not_false, Bool.true_or, and_self]
  · rw [CFSG.KS.Raw.Orb.strictB_eq] at hK
    generalize pc (SuzRgU c) (QE j) = RK at hK hR
    obtain ⟨-, hK⟩ := and_t hK
    obtain ⟨hD, hK⟩ := and_t hK
    obtain ⟨hC, hS⟩ := and_t hK
    obtain ⟨hS0, hS1⟩ := and_t hS
    refine ⟨?_, ?_, ?_, st_ok (by norm_num) hR hS0, st_ok (by norm_num) hR hS1⟩
    · obtain ⟨hm, hD⟩ := and_t hD
      obtain ⟨hi, hD⟩ := and_t hD
      unfold decB anyBelow
      refine Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2 ⟨_, List.mem_range.2
        (Nat.blt_eq.mp hm), List.any_eq_true.2 ⟨_, List.mem_range.2 (Nat.blt_eq.mp hi), ?_⟩⟩))
      rw [eqComp_P hR (pPT (Nat.blt_eq.mp hm)) (pQ (by have := Nat.blt_eq.mp hi; omega)), hD]
    · rw [CFSG.KS.Raw.Orb.bIf_eq, inV_iff] at hC
      unfold cenB
      split_ifs at hC with hv
      · rw [hv]
        simp
      · obtain ⟨hi, hC⟩ := and_t hC
        obtain ⟨hp, -⟩ := and_t hC
        unfold ncAt at hp
        obtain ⟨hz, hne⟩ := and_t hp
        have hi' := Nat.blt_eq.mp hi
        have hf := comm_false hR (pT hi') (Nat.blt_eq.mp hz) (not_t hne)
        have hall : ((List.range 8).all fun i => rigComm (rigRTab c j) (rigTTab i)) = false :=
          List.all_eq_false.2 ⟨_, List.mem_range.2 hi', by rw [hf]; decide⟩
        rw [hall]
        simp
    · rw [CFSG.KS.Raw.Orb.bIf_eq, inV_iff] at hC
      unfold x1B
      split_ifs at hC with hv
      · rw [hv]
        simp
      · obtain ⟨-, hC⟩ := and_t hC
        obtain ⟨-, hx⟩ := and_t hC
        rw [commV_false hR pV0 (ncv4_spec hx)]
        simp

theorem rigDecompOK_true : rigDecompOK = true := by
  unfold rigDecompOK
  exact all2 fun c hc j hj => (cell_facts hc hj).1

theorem rigCenterOK_true : rigCenterOK = true := by
  unfold rigCenterOK
  exact all2 fun c hc j hj => (cell_facts hc hj).2.1

theorem rigX1OK_true : rigX1OK = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (pc (SuzRgV 0) W) (pc W (SuzRgV 0)))
    (Nat.beq (cWK (rigX1 ++ rigX1 ++ rigX1 ++ rigX1 ++ rigX1)) Id)).1 kX1
  unfold rigX1OK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by decide, ?_⟩, ?_⟩, all2 fun c hc j hj => (cell_facts hc hj).2.2.1⟩
  · rw [comm_P pV0 SuzFb.pW]
    exact h1
  · rw [eqA_P (cWord_P _ (by decide)) pidn_P]
    exact h2

theorem conj_P {x y r : Array Nat} {X Y R : Nat} (hx : P x X) (hy : P y Y) (hr : P r R) :
    (allLt 1782 fun z => x[y[z]!]! == r[x[z]!]!) = Nat.beq (pc X Y) (pc R X) := by
  rw [← eqA_P (p_comp hx hy) (p_comp hr hx)]
  unfold eqA
  refine SuzFb.allLt_congr' fun z hz => ?_
  rw [CFSG.Monster.B.Co2.compA_get hz, CFSG.Monster.B.Co2.compA_get hz]

theorem rigGenOK_true : rigGenOK = true := by
  unfold rigGenOK
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have hk := allN_spec kGen i hi'
  have hT := pT hi'
  obtain ⟨hc, hj, -⟩ := kT' hi'
  rw [ttab_eq] at hT
  unfold genK at hk
  unfold gen at hk hT hc hj
  generalize rigGens.getD i (0, [], 0, 0) = t at hk hT hc hj ⊢
  obtain ⟨s, u, c, j⟩ := t
  dsimp only at hk hT hc hj ⊢
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at hk
  obtain ⟨h1, hk⟩ := and_t hk
  obtain ⟨h2, hk⟩ := and_t hk
  obtain ⟨h3, hk⟩ := and_t hk
  obtain ⟨h4, h5⟩ := and_t hk
  have hs := Nat.blt_eq.mp h1
  have hu := SuzFb.letters h2
  have hC := cWord_P u hu
  rw [comm_P hC SuzFb.pW, h3, comm_P hT SuzFb.pW, h4, conj_P hC (pSK hs) hT, h5]
  simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hs, hc⟩, hj⟩, List.all_eq_true.2 fun k hk => decide_eq_true (hu k hk)⟩

theorem rigCommOK_true : rigCommOK = true := by
  unfold rigCommOK
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro k hk
  have hi' := List.mem_range.1 hi
  have hk' := List.mem_range.1 hk
  have h := allN_spec (allN_spec kComm i hi') k hk'
  unfold commK at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at h
  obtain ⟨h1, h2⟩ := and_t h
  exact commV_true (pT hi') (pT hk') (Nat.blt_eq.mp h1) h2

theorem gam_eq {s : Nat} (hs : s < 2) : rigGam.getD s [] = [gam s 0, gam s 1] := by
  interval_cases s <;> rfl

theorem stab_body {s c₀ j₀ : Nat} (hs : s < 2) (ht : rigSeeds.getD s (0, 0) = (c₀, j₀))
    (hc : c₀ < 16) (hj : j₀ < 128) :
    (decide (c₀ < 16) && decide (j₀ < 128) && rigComm (rigRTab c₀ j₀) w0Tab &&
      rigInV (compA 1782 (rigSTab s) (rigSTab s)) &&
      (rigGam.getD s []).all (fun g => g.all (fun k => decide (k < 10)) &&
        rigComm (cWord g) w0Tab && rigCommV (cWord g) (rigSTab s)) &&
      (List.range 16).all fun c => allLt 128 fun j => stB s c j) = true := by
  have hst : rigSTab s = rigRTab c₀ j₀ := by
    unfold rigSTab
    rw [ht]
  obtain ⟨hsd, -⟩ := seed_facts hs
  unfold seedK at hsd
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at hsd
  obtain ⟨hcw, hsq⟩ := and_t hsd
  obtain ⟨hi4, hsqe⟩ := and_t hsq
  have hgm : ∀ g < 2, ((gam s g).all (fun k => decide (k < 10)) &&
      rigComm (cWord (gam s g)) w0Tab && rigCommV (cWord (gam s g)) (rigSTab s)) = true := by
    intro g hg
    obtain ⟨hl, hcg, i, hi, hv⟩ := gam_facts hs hg
    rw [comm_P (pG hs hg) SuzFb.pW, hcg, commV_true (pG hs hg) (pSK hs) hi hv,
      List.all_eq_true.2 fun k hk => decide_eq_true (hl k hk)]
    rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hc, hj⟩, ?_⟩, ?_⟩, ?_⟩, all2 fun c hc j hj => ?_⟩
  · rw [← hst, comm_P (pSK hs) SuzFb.pW]
    exact hcw
  · unfold rigInV anyBelow
    refine List.any_eq_true.2 ⟨_, List.mem_range.2 (Nat.blt_eq.mp hi4), ?_⟩
    rw [eqA_P (pSS hs) (pQ (by have := Nat.blt_eq.mp hi4; omega))]
    exact hsqe
  · rw [gam_eq hs, List.all_cons, List.all_cons, List.all_nil, hgm 0 (by norm_num),
      hgm 1 (by norm_num)]
    rfl
  · interval_cases s
    exacts [(cell_facts hc hj).2.2.2.1, (cell_facts hc hj).2.2.2.2]

theorem rigStabOK_true : rigStabOK = true := by
  unfold rigStabOK
  rw [List.all_eq_true]
  intro s hs
  have hs' := List.mem_range.1 hs
  interval_cases s
  · exact stab_body (c₀ := 0) (j₀ := 24) (by norm_num) rfl (by norm_num) (by norm_num)
  · exact stab_body (c₀ := 6) (j₀ := 0) (by norm_num) rfl (by norm_num) (by norm_num)

theorem perp {v : Nat} (hv : v < 64) : (rigBil v != 0) = !(perpK v) := by
  have h := allN_spec kN v hv
  rw [beq_iff_eq] at h
  rw [h]
  rfl

theorem uTest_eq (X : Nat) : rigUTest (unpack 64 7 X) = uTestK X := by
  unfold rigUTest uTestK
  rw [CFSG.KC.HeFixK.unpack_getElem! (by norm_num : 1 < 64), SuzFb.beqN, CFSG.KS.Raw.Orb.bAnd_eq]
  congr 1
  refine SuzFb.allLt_allN fun v hv => ?_
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq]
  rw [CFSG.KC.HeFixK.unpack_getElem! hv, perp hv, SuzFb.beqN, SuzFb.beqN]
  have ex : Nat.xor v 1 = v ^^^ 1 := rfl
  rw [ex]
  cases perpK v <;> cases Nat.beq (pg 7 (mask 7) X v) v <;>
    cases Nat.beq (pg 7 (mask 7) X v) (v ^^^ 1) <;> rfl

theorem agree_eq (X M : Nat) : rigAgree (unpack 64 7 X) (unpack 64 7 M) = agreeK X M := by
  unfold rigAgree agreeK
  refine SuzFb.allLt_allN fun v hv => ?_
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq]
  rw [CFSG.KC.HeFixK.unpack_getElem! hv, CFSG.KC.HeFixK.unpack_getElem! hv, perp hv, SuzFb.beqN,
    SuzFb.beqN]
  have ex : Nat.xor (pg 7 (mask 7) M v) 1 = pg 7 (mask 7) M v ^^^ 1 := rfl
  rw [ex]
  cases perpK v <;> cases Nat.beq (pg 7 (mask 7) X v) (pg 7 (mask 7) M v) <;>
    cases Nat.beq (pg 7 (mask 7) X v) (pg 7 (mask 7) M v ^^^ 1) <;> rfl

theorem pM {k : Nat} (hk : k < 60) :
    matWord (rigExpand (rigBfs.getD k [])) = unpack 64 7 (SuzRgM k) ∧ cn7 (SuzRgM k) = true := by
  obtain ⟨h1, h2⟩ := and_t (allN_spec kM k hk)
  rw [Nat.eq_of_beq_eq_true h2]
  exact SuzFb.matWord_eq (SuzFb.letters h1)

theorem rigLiftOK_true : rigLiftOK = true := by
  unfold rigLiftOK
  rw [List.all_eq_true]
  intro c hc
  have hc' := List.mem_range.1 hc
  obtain ⟨h1, h2⟩ := and_t (allN_spec kLift c hc')
  obtain ⟨h3, h4⟩ := and_t h2
  have hw := (kU' hc').1
  rw [List.all_eq_true.2 fun k hk => decide_eq_true (hw k hk), comm_P (pU hc') SuzFb.pW, h1,
    (SuzFb.matWord_eq hw).1, uTest_eq, h3, SuzFb.beqN, SuzFb.beqN]
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h4
  cases h5 : Nat.beq (rigUFix.getD c 0) 0 <;> simp_all

theorem rigX2OK_true : rigX2OK = true := by
  obtain ⟨h1, h⟩ := (bAnd_iff (SuzFb.lettersK rigX2)
    (bAnd(Nat.beq (pc (cWK rigX2) W) (pc W (cWK rigX2)),
      uTestK (SuzFb.mWK (rigX2 ++ rigX2 ++ rigX2))))).1 kX2
  obtain ⟨h2, h3⟩ := (bAnd_iff (Nat.beq (pc (cWK rigX2) W) (pc W (cWK rigX2)))
    (uTestK (SuzFb.mWK (rigX2 ++ rigX2 ++ rigX2)))).1 h
  have hw := SuzFb.letters h1
  have hw3 : ∀ k ∈ rigX2 ++ rigX2 ++ rigX2, k < 10 := by decide
  unfold rigX2OK
  rw [comm_P (cWord_P _ hw) SuzFb.pW, h2, (SuzFb.matWord_eq hw3).1, uTest_eq, h3]
  decide

theorem up_mem {i : Nat} (h : SuzFb.memK SuzRgUP i = true) : ∃ c < 16, nget SuzRgUP c = i := by
  obtain ⟨c, hc, e⟩ := List.getElem_of_mem (SuzFb.memK_iff.1 h)
  exact ⟨c, by rw [kUPLen] at hc; exact hc, by rw [nget_get _ hc]; exact e⟩

theorem rigUCompleteOK_true : rigUCompleteOK = true := by
  unfold rigUCompleteOK
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_
  rw [SuzFb.tab_get hi, uTest_eq]
  cases hu : uTestK (SuzFbE.T i)
  · rfl
  · have hs : i / 1620 < 16 := by omega
    have h := ucSlAll (i / 1620) hs
    unfold ucSl at h
    have h2 := allN_spec h (i % 1620) (Nat.mod_lt _ (by norm_num))
    beta_reduce at h2
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h2
    have e : Nat.add (Nat.mul 1620 (i / 1620)) (i % 1620) = i := Nat.div_add_mod i 1620
    rw [e, hu] at h2
    obtain ⟨c, hc, hci⟩ := up_mem h2
    obtain ⟨-, h4⟩ := and_t (allN_spec kUP c hc)
    obtain ⟨hm, hcn⟩ := SuzFb.matWord_eq (kU' hc).1
    unfold anyBelow
    refine Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2 ⟨c, List.mem_range.2 hc, ?_⟩))
    rw [hm, beq_unpack (SuzFb.canT hi) hcn, ← hci]
    exact h4

theorem bfs_len : rigBfs.length = 60 := rfl

theorem rigBfsOK_true : rigBfsOK = true := by
  unfold rigBfsOK
  dsimp only
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_
  rw [SuzFb.tab_get hi, CFSG.KC.HeFixK.unpack_getElem! (by norm_num : 1 < 64)]
  have hs : i / 320 < 81 := by omega
  have h := bfSlAll (i / 320) hs
  unfold bfSl at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at h
  have h2 := allN_spec h (i % 320) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h2
  have e : Nat.add (Nat.mul 320 (i / 320)) (i % 320) = i := Nat.div_add_mod i 320
  rw [e, CFSG.KS.Raw.Orb.bIf_eq] at h2
  generalize pg 6 (mask 6) (SuzRgBW (i / 320)) (i % 320) = k at h2
  by_cases h1 : Nat.beq (pg 7 (mask 7) (SuzFbE.T i) 1) 1 = true
  · simp only [h1, ↓reduceIte] at h2
    obtain ⟨hk, hag⟩ := and_t h2
    have hk' := Nat.blt_eq.mp hk
    obtain ⟨hm, -⟩ := pM hk'
    refine Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2 ⟨_, List.mem_map.2
      ⟨rigBfs.getD k [], ?_, rfl⟩, ?_⟩))
    · rw [List.getD_eq_getElem _ _ (by rw [bfs_len]; exact hk')]
      exact List.getElem_mem _
    · rw [hm, agree_eq]
      exact hag
  · rw [bne, SuzFb.beqN, Bool.eq_false_iff.2 h1]
    rfl

theorem wmap {v : Nat} (hv : v < 64) :
    ((rigIrrWords.map fun u => matWord (rigExpand u)).map fun m => m[v]!) =
      (List.range 8).map fun k => pg 7 (mask 7) (SuzRgM k) v := by
  rw [kIrr, List.map_map, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.1 hk
  rw [Function.comp_apply, Function.comp_apply, (pM (by omega : k < 60)).1,
    CFSG.KC.HeFixK.unpack_getElem! hv]

theorem rigIrredOK_true : rigIrredOK = true := by
  unfold rigIrredOK
  dsimp only
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun v hv => ?_
  have h := irKAll v hv
  unfold irK at h
  rw [perp hv]
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  by_cases hp : perpK v = true
  · simp only [hp, ↓reduceIte] at h
    rw [CFSG.KS.Raw.Orb.bIf_eq] at h
    by_cases h1 : Nat.blt 1 v = true
    · simp only [h1, ↓reduceIte] at h
      simp only [CFSG.KS.Raw.Orb.strictB_eq] at h
      have key : (allLt 64 fun u => rigBil u != 0 ||
          anyBelow 512 fun m => rigXor (bvec v) m == u) = true := by
        refine CFSG.Monster.B.Co2.allLt_iff.2 fun u hu => ?_
        have h2 := allN_spec h u hu
        beta_reduce at h2
        rw [CFSG.KS.Raw.Orb.bIf_eq] at h2
        rw [perp hu]
        by_cases hq : perpK u = true
        · simp only [hq, ↓reduceIte] at h2
          obtain ⟨hm, hx⟩ := and_t h2
          unfold anyBelow
          exact Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2
            ⟨_, List.mem_range.2 (Nat.blt_eq.mp hm), hx⟩))
        · rw [Bool.eq_false_iff.2 hq]
          rfl
      unfold bvec at key
      rw [wmap hv, key, Bool.or_true]
    · have hv1 : v ≤ 1 := by
        rcases Nat.lt_or_ge 1 v with h' | h'
        · exact absurd (Nat.blt_eq.mpr h') h1
        · exact h'
      refine Bool.or_eq_true_iff.2 (Or.inl (Bool.or_eq_true_iff.2 ?_))
      interval_cases v
      · exact Or.inl (Bool.or_eq_true_iff.2 (Or.inr rfl))
      · exact Or.inr rfl
  · rw [Bool.eq_false_iff.2 hp]
    rfl

theorem checks : rigLiftOK = true ∧ rigUCompleteOK = true ∧ rigGenOK = true ∧ rigCommOK = true ∧
    rigDecompOK = true ∧ rigCenterOK = true ∧ rigStabOK = true ∧ rigX1OK = true ∧
    rigX2OK = true ∧ rigBfsOK = true ∧ rigIrredOK = true :=
  ⟨rigLiftOK_true, rigUCompleteOK_true, rigGenOK_true, rigCommOK_true, rigDecompOK_true,
    rigCenterOK_true, rigStabOK_true, rigX1OK_true, rigX2OK_true, rigBfsOK_true,
    rigIrredOK_true⟩

end CertificateChecks.KernelSpor.SuzRg

end
