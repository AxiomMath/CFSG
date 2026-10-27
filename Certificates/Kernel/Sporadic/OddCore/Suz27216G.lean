module

public import Certificates.Kernel.Sporadic.OddCore.Suz27216K
public import Certificates.Kernel.Sporadic.SuzInv.Inner0
public import CFSG.Certificates.Kernel.Spor.Suz27216Sound
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Scan
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Sporadic.SuzOddCore.OddCore
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N27216

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PEnum CFSG.KS.Suz27216
  CFSG.KS.SporSch CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.SuzN0 CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor
  CFSG.KS.Prim CFSG.Monster.B.Co2
open scoped commutatorElement

local notation "PR" => PRep 1782 11

theorem prep_unique {P : Nat} {g h : Equiv.Perm (Fin 1782)} (hg : PR P g) (hh : PR P h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_one : PR (pidn 1782 11) 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_at {P : Nat} {g : Equiv.Perm (Fin 1782)} (h : PR P g) (x : Nat) (hx : x < 1782) :
    pg 11 (mask 11) P x = (g ⟨x, hx⟩ : Nat) := h ⟨x, hx⟩

theorem tabRep_of_prep {P : Nat} {g : Equiv.Perm (Fin 1782)} (h : PR P g) :
    TabRep (unpack 1782 11 P) g :=
  ⟨by simp [unpack], fun i => by rw [CFSG.KS.Raw.Orb.unpack_get i.2, h i]⟩

@[expose] def codeOf (l : ℤ) : Nat := if 0 < l then l.toNat - 1 else (-l).toNat + 4

theorem letP_codeOf {l : ℤ} (hl : l ≠ 0 ∧ -5 ≤ l ∧ l ≤ 5) :
    letP (invInnerGen 0) (codeOf l) = letterElt l := by
  unfold letP codeOf letterElt xElt
  by_cases hp : 0 < l
  · have h5 : l.toNat - 1 < 5 := by omega
    simp only [hp, ↓reduceIte, h5]
  · have h5 : ¬ ((-l).toNat + 4 < 5) := by omega
    have e : (-l).toNat + 4 - 5 + 2 = (-l).toNat - 1 + 2 := by omega
    simp only [hp, ↓reduceIte, h5, e]

theorem wordP_map : ∀ L : List ℤ, (∀ l ∈ L, l ≠ 0 ∧ -5 ≤ l ∧ l ≤ 5) →
    wordP (invInnerGen 0) (L.map codeOf) = wordElt L
  | [], _ => rfl
  | l :: L, h => by
    have ih := wordP_map L fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold wordP wordElt at ih ⊢
    simp only [List.map_cons, List.prod_cons]
    rw [ih, letP_codeOf (h l List.mem_cons_self)]

theorem codes_eq : ∀ k < 9, (oddWords.getD k ([], 1)).1.map codeOf = oddCodes.getD k [] := by
  decide

theorem exps_eq : ∀ k < 9, (oddWords.getD k ([], 1)).2 = oddExps.getD k 0 := by decide

theorem zcode_eq : zWord.map codeOf = zCode := by decide

theorem letters_ok : ∀ k < 9, ∀ l ∈ (oddWords.getD k ([], 1)).1, l ≠ 0 ∧ -5 ≤ l ∧ l ≤ 5 := by
  decide

theorem zletters_ok : ∀ l ∈ zWord, l ≠ 0 ∧ -5 ≤ l ∧ l ≤ 5 := by decide

theorem code3_bit (p0 p1 p2 i : Nat) : (code3 p0 p1 p2).testBit i =
    (p0.testBit i || ((decide (i ≥ 11) && p1.testBit (i - 11)) ||
      (decide (i ≥ 22) && p2.testBit (i - 22)))) := by
  have e : code3 p0 p1 p2 = p0 ||| (p1 <<< 11 ||| p2 <<< 22) := rfl
  rw [e, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]

theorem testBit_small {i x : Nat} (hi : 11 ≤ i) (hx : x < 2048) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx
    (le_trans (by norm_num : 2048 ≤ 2 ^ 11) (Nat.pow_le_pow_right (by norm_num) hi)))

theorem code3_inj {a0 a1 a2 b0 b1 b2 : Nat} (ha0 : a0 < 2048) (ha1 : a1 < 2048)
    (hb0 : b0 < 2048) (hb1 : b1 < 2048) (h : code3 a0 a1 a2 = code3 b0 b1 b2) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  have hb : ∀ i, (code3 a0 a1 a2).testBit i = (code3 b0 b1 b2).testBit i := fun i => by rw [h]
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, Nat.eq_of_testBit_eq fun i => ?_,
    Nat.eq_of_testBit_eq fun i => ?_⟩
  · by_cases hi : i < 11
    · have e := hb i
      have d1 : decide (i ≥ 11) = false := decide_eq_false (by omega)
      have d2 : decide (i ≥ 22) = false := decide_eq_false (by omega)
      simp only [code3_bit, d1, d2, Bool.false_and, Bool.or_false] at e
      exact e
    · rw [testBit_small (by omega) ha0, testBit_small (by omega) hb0]
  · by_cases hi : i < 11
    · have e := hb (i + 11)
      have d1 : decide (i + 11 ≥ 11) = true := decide_eq_true (by omega)
      have d2 : decide (i + 11 ≥ 22) = false := decide_eq_false (by omega)
      simp only [code3_bit, d1, d2, Bool.false_and, Bool.or_false, Bool.true_and,
        testBit_small (by omega : 11 ≤ i + 11) ha0, testBit_small (by omega : 11 ≤ i + 11) hb0,
        Bool.false_or, Nat.add_sub_cancel] at e
      exact e
    · rw [testBit_small (by omega) ha1, testBit_small (by omega) hb1]
  · have e := hb (i + 22)
    have d1 : decide (i + 22 ≥ 11) = true := decide_eq_true (by omega)
    have d2 : decide (i + 22 ≥ 22) = true := decide_eq_true (by omega)
    have e1 : i + 22 - 11 = i + 11 := by omega
    simp only [code3_bit, d1, d2, e1, Bool.true_and, Nat.add_sub_cancel,
      testBit_small (by omega : 11 ≤ i + 22) ha0, testBit_small (by omega : 11 ≤ i + 22) hb0,
      testBit_small (by omega : 11 ≤ i + 11) ha1, testBit_small (by omega : 11 ≤ i + 11) hb1,
      Bool.false_or] at e
    exact e

section Glue


theorem prep_Gi {j : Nat} (hj : j < 7) : PR (Gi j) (invInnerGen 0 j) := by
  have hj' : j < (invInnerGenArrs 0).size := by rw [SuzInv.gensI0.1]; omega
  have hr := rep_invInnerGen (i := 0) (by norm_num) hj'
  rw [SuzInv.gensI0.2 j (by omega)] at hr
  exact prep_of_rep hr

theorem words_facts : (∀ k < 9, canonK 1782 11 (mask 11) (1782 * 11) (OW k) = true ∧
      PR (OW k) (oddElt k) ∧ oddElt k ^ (oddWords.getD k ([], 1)).2 = 1) ∧ PR (OW 9) zElt := by
  obtain ⟨h1, h2⟩ := wordsK_sound (n := 1782) (w := 11) (g := invInnerGen 0) (by norm_num)
    (by norm_num) k_words (fun j hj => prep_Gi hj)
  have e : ∀ k < 9, wordP (invInnerGen 0) (oddCodes.getD k []) = oddElt k := fun k hk => by
    rw [← codes_eq k hk, wordP_map _ (letters_ok k hk)]
    rfl
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨c, p, pw⟩ := h1 k hk
    rw [e k hk] at p pw
    rw [exps_eq k hk]
    exact ⟨c, p, pw⟩
  · rw [← zcode_eq, wordP_map _ zletters_ok] at h2
    exact h2

theorem prep_t1 : PR (SuzTP 1) (suzInv 1) := by
  have h := rep_suzInv (i := 1) (by norm_num)
  rw [(OddCore.rep_facts (i := 1) (by norm_num)).1] at h
  exact prep_of_rep h

theorem mem_M {P : Nat} {g : Equiv.Perm (Fin 1782)}
    (hc : canonK 1782 11 (mask 11) (1782 * 11) P = true) (hP : PR P g)
    (hs : OddCore.msift P = true) : g ∈ suzM := by
  have h := OddCore.inM_eq (g := unpack 1782 11 P) rfl hc
  rw [hs] at h
  exact (inM_iff (rep_unpack hP)).1 h

theorem mem_D_of {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (ht : s * suzInv 1 = suzInv 1 * s) : s ∈ invD 1 := by
  rw [invD_eq_centT (i := 1) (by norm_num)]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 ht, suzM_le_suzT hs⟩

@[expose] noncomputable def TT (i a : Nat) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (unpack 1782 11 (trK 1782 (1782 * 11) SuzInvF1.LR SuzInvF1.TR i a))

theorem lev_size {i : Nat} (hi : i < 3) :
    (levD1 ())[i]!.pts.size = rcnt (SuzInvF1.LR i) :=
  (levelTr_sound SuzInv.bindsF1 SuzInvF1.head SuzInvF1.hl hi).1

theorem lev_facts {i a : Nat} (hi : i < 3) (ha : a < rcnt (SuzInvF1.LR i)) :
    (levD1 ())[i]!.tr[a]! = unpack 1782 11 (trK 1782 (1782 * 11) SuzInvF1.LR SuzInvF1.TR i a) ∧
    PR (trK 1782 (1782 * 11) SuzInvF1.LR SuzInvF1.TR i a) (TT i a) ∧
    PR (triK 1782 (1782 * 11) SuzInvF1.LR SuzInvF1.TRI i a) (TT i a)⁻¹ := by
  have hp := (Orb.head_facts SuzInvF1.head).1
  have hbl := Orb.base_lt_of_levels SuzInv.bindsF1 SuzInvF1.hl
  obtain ⟨-, P⟩ := Orb.agree_levelK SuzInv.bindsF1 hp hbl (R := SuzInvF1.LR)
    (TRI := SuzInvF1.TRI) hi (SuzInvF1.hl i hi)
  exact ⟨(levelTr_sound SuzInv.bindsF1 SuzInvF1.head SuzInvF1.hl hi).2 a ha, (P a ha).1,
    (P a ha).2⟩

theorem decomp {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invD 1) : ∃ a b c : Nat,
    a < rcnt (SuzInvF1.LR 0) ∧ b < rcnt (SuzInvF1.LR 1) ∧ c < rcnt (SuzInvF1.LR 2) ∧
    g = TT 0 a * TT 1 b * TT 2 c := by
  obtain ⟨a, b, c, A, B, C, ha, hb, hc, hA, hB, hC, rfl⟩ := invD1_prod3 hg
  rw [lev_size (by norm_num)] at ha hb hc
  rw [(lev_facts (by norm_num) ha).1] at hA
  rw [(lev_facts (by norm_num) hb).1] at hB
  rw [(lev_facts (by norm_num) hc).1] at hC
  refine ⟨a, b, c, ha, hb, hc, ?_⟩
  rw [prep_unique (prep_of_rep hA) (lev_facts (by norm_num) ha).2.1,
    prep_unique (prep_of_rep hB) (lev_facts (by norm_num) hb).2.1,
    prep_unique (prep_of_rep hC) (lev_facts (by norm_num) hc).2.1]

theorem pid_at (x : Nat) (hx : x < 1782) : pg 11 (mask 11) (pidn 1782 11) x = x :=
  CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hx

section Base

variable {LR TR : Nat → Nat} {T : Nat → Nat → Equiv.Perm (Fin 1782)}
  (hch : chainK 1782 11 LR TR = true)
  (hT : ∀ i < 3, ∀ a < rcnt (LR i), PR (trK 1782 (1782 * 11) LR TR i a) (T i a))
include hch

local notation "chainF" => chainK_parts hch

include hT in
theorem tt_one {i a : Nat} (hi : i < 3) (ha : a < rcnt (LR i)) (h0 : a = 0) : T i a = 1 := by
  subst h0
  refine prep_unique (hT i hi 0 ha) ?_
  rw [chainF.1 i hi]
  exact prep_one

theorem pos0 {a : Nat} (ha : a < rcnt (LR 0))
    (hf : pg 11 (mask 11) (trK 1782 (1782 * 11) LR TR 0 a) 0 = 0) : a = 0 := by
  have e1 := chainF.2.1 a ha
  have e0 := chainF.2.1 0 (by omega)
  rw [chainF.1 0 (by norm_num), pid_at 0 (by norm_num)] at e0
  rw [hf] at e1
  omega

theorem pos1 {b : Nat} (hb : b < rcnt (LR 1))
    (hf : pg 11 (mask 11) (trK 1782 (1782 * 11) LR TR 1 b) 1 = 1) : b = 0 := by
  have e1 := (chainF.2.2.1 b hb).2
  have e0 := (chainF.2.2.1 0 (by omega)).2
  rw [chainF.1 1 (by norm_num), pid_at 1 (by norm_num)] at e0
  rw [hf] at e1
  omega

theorem pos2 {c : Nat} (hc : c < rcnt (LR 2))
    (hf : pg 11 (mask 11) (trK 1782 (1782 * 11) LR TR 2 c) 2 = 2) : c = 0 := by
  have e1 := (chainF.2.2.2 c hc).2.2
  have e0 := (chainF.2.2.2 0 (by omega)).2.2
  rw [chainF.1 2 (by norm_num), pid_at 2 (by norm_num)] at e0
  rw [hf] at e1
  omega

include hT in
theorem eq_one_gen {a b c : Nat} (ha : a < rcnt (LR 0)) (hb : b < rcnt (LR 1))
    (hc : c < rcnt (LR 2)) (hf : Fix3 (n := 1782) (by norm_num) (T 0 a * T 1 b * T 2 c)) :
    T 0 a * T 1 b * T 2 c = 1 := by
  have pA := hT 0 (by norm_num) a ha
  have pB := hT 1 (by norm_num) b hb
  have pC := hT 2 (by norm_num) c hc
  have fC0 : T 2 c ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
    Fin.ext (by rw [← prep_at pC 0 (by norm_num)]; exact (chainF.2.2.2 c hc).1)
  have fC1 : T 2 c ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ :=
    Fin.ext (by rw [← prep_at pC 1 (by norm_num)]; exact (chainF.2.2.2 c hc).2.1)
  have fB0 : T 1 b ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ :=
    Fin.ext (by rw [← prep_at pB 0 (by norm_num)]; exact (chainF.2.2.1 b hb).1)
  have h0 := hf 0 (by norm_num)
  simp only [Equiv.Perm.mul_apply, fC0, fB0] at h0
  have ha0 : a = 0 := pos0 hch ha (by rw [prep_at pA 0 (by norm_num)]; exact h0)
  rw [tt_one hch hT (by norm_num) ha ha0] at hf ⊢
  have h1 := hf 1 (by norm_num)
  simp only [one_mul, Equiv.Perm.mul_apply, fC1] at h1
  have hb0 : b = 0 := pos1 hch hb (by rw [prep_at pB 1 (by norm_num)]; exact h1)
  rw [tt_one hch hT (by norm_num) hb hb0] at hf ⊢
  have h2 := hf 2 (by norm_num)
  simp only [one_mul] at h2
  have hc0 : c = 0 := pos2 hch hc (by rw [prep_at pC 2 (by norm_num)]; exact h2)
  rw [tt_one hch hT (by norm_num) hc hc0, one_mul, one_mul]

end Base

theorem eq_one_of_fix {g : Equiv.Perm (Fin 1782)} (hg : g ∈ invD 1)
    (hf : Fix3 (by norm_num) g) : g = 1 := by
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := decomp hg
  exact eq_one_gen k_chain (fun i hi a ha => (lev_facts hi ha).2.1) ha hb hc hf

theorem fix_one : Fix3 (n := 1782) (by norm_num) 1 := fun _ _ => rfl

theorem facts : SuzN0Facts := by
  obtain ⟨hw, hz⟩ := words_facts
  have hO : ∀ k < 9, PR (OW k) (oddElt k) := fun k hk => (hw k hk).2.1
  obtain ⟨hG, ⟨qz, hqz, hTz⟩, hconjR⟩ := rK_sound (n := 1782) (w := 11) (by norm_num) k_r hO
  have hRj : ∀ j < 4, PR (RE.G j) (rElt j) := fun j hj => by
    rw [hG j hj]
    exact prep_pcomp (by norm_num) (hO _ (by omega)) (hO _ (by omega))
  obtain ⟨hp, hHP, hcan, hms, hhc, hGN⟩ := hK_sound (n := 1782) (w := 11) (by norm_num) k_h
    prep_t1 hz (hO 8 (by norm_num)) hRj
  have hk4 : RE.k = 4 := Nat.eq_of_beq_eq_true k_ek
  have hc64 : RE.cnt = 64 := Nat.eq_of_beq_eq_true k_ecnt
  let gens : Array Tab := Array.ofFn (n := 4) fun j => unpack 1782 11 (RE.G j.val)
  have hgsz : gens.size = 4 := by simp [gens]
  have hget : ∀ j < 4, gens[j]! = unpack 1782 11 (RE.G j) := fun j hj => by
    rw [getElem!_pos gens j (by omega), Array.getElem_ofFn]
  have hcanG : ∀ j < 4, canonK 1782 11 (mask 11) (1782 * 11) (RE.G j) = true := fun j hj => by
    rw [hG j hj]
    exact CFSG.KC.BfsPin.canonK_pcomp (hw _ (by omega)).1 (hw _ (by omega)).1
  have hgok : GensOK 1782 11 RE.k RE.G gens :=
    ⟨by rw [hk4, hgsz], fun j hj => ⟨hget j (by omega), hcanG j (by omega)⟩⟩
  have hpt : ∀ i < RE.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false RE.G RE.GI RE.k RE.cnt
      RE.T RE.PL RE.POS RE.SRT RE.SRI i = true := by
    intro i hi
    have h1 := allN_spec k_esl i (by omega)
    rw [strictB_app'] at h1
    have e : Nat.add 0 i = i := Nat.zero_add i
    have hlt : Nat.blt i RE.cnt = true := Nat.blt_eq.mpr hi
    rw [e, hlt] at h1
    exact h1
  have henum := (penumK_left_sound (cap := 64) (by rfl) hgok k_eh hpt).2
  have hE : Enumerates RR (penumRec 1782 11 RE.cnt RE.T RE.PL).tabs.toList :=
    enumerates_closure (A := Set.range fun i : Fin 4 => rElt i) (gens := gens)
      (fun a ha => by
        obtain ⟨i, rfl⟩ := ha
        exact ⟨i, by rw [hgsz]; exact i.2, by rw [hget i i.2]; exact tabRep_of_prep (hRj i i.2)⟩)
      (fun j hj => by
        rw [hgsz] at hj
        exact ⟨rElt j, ⟨⟨j, hj⟩, rfl⟩, by rw [hget j hj]; exact tabRep_of_prep (hRj j hj)⟩)
      henum
  have hmem : ∀ q < 64, ∀ g, PR (RE.T q) g → g ∈ RR := by
    intro q hq g hg
    have hq' : q < (penumRec 1782 11 RE.cnt RE.T RE.PL).tabs.size := by
      simp [penumRec, hc64, hq]
    obtain ⟨g', hg', hrep⟩ := hE.sound _ (getElem!_mem hq')
    have e : (penumRec 1782 11 RE.cnt RE.T RE.PL).tabs[q]! = unpack 1782 11 (RE.T q) := by
      rw [getElem!_pos _ q hq']
      simp [penumRec]
    rw [e] at hrep
    rw [hrep.perm_eq (tabRep_of_prep hg)] at hg'
    exact hg'
  have hcard : Nat.card RR = 64 := by
    rw [hE.card]
    simp [penumRec, hc64]
  have hzR : zElt ∈ RR := hmem qz hqz _ (by rw [hTz]; exact hz)
  have hwR : ∀ i < 4, wElt * rElt i * wElt⁻¹ ∈ RR := fun i hi => by
    obtain ⟨q, hq, hrep⟩ := hconjR i hi
    exact hmem q hq _ hrep
  have hGNe : ∀ j < 5, PR (GN j) (gensElt hp j) := by
    intro j hj
    have e := hGN j hj
    by_cases h4 : j < 4
    · simp only [h4, ↓reduceIte] at e
      simp only [gensElt, h4, ↓reduceIte]
      exact e
    · simp only [h4, ↓reduceIte] at e
      simp only [gensElt, h4, ↓reduceIte]
      exact e
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ := survK_sound (n := 1782) (w := 11) (M := suzM)
    (by norm_num) (by norm_num) (fun P g hc hP hs => mem_M hc hP hs) prep_t1 k_surv
  have hSD : ∀ s ∈ S, s ∈ invD 1 := fun s hs => mem_D_of (hS2 s hs).1 (hS2 s hs).2.1
  have hSF : SurvFacts S := by
    refine ⟨fun s hs => (hS2 s hs).1, fun s hs => ?_, fun s hs t ht => ?_,
      fun s hs t ht hs2 ht2 => ?_, ?_⟩
    · have hD := hSD s hs
      rcases (hS2 s hs).2.2 with h | h
      · exact Or.inl (eq_one_of_fix ((invD 1).mul_mem hD hD) h)
      · exact Or.inr (eq_one_of_fix ((invD 1).mul_mem ((invD 1).mul_mem hD hD) hD) h)
    · have hs' := hSD s hs
      have ht' := hSD t ht
      have hc : ⁅s, t⁆ ∈ invD 1 := by
        rw [commutatorElement_def]
        exact (invD 1).mul_mem ((invD 1).mul_mem ((invD 1).mul_mem hs' ht')
          ((invD 1).inv_mem hs')) ((invD 1).inv_mem ht')
      exact eq_one_of_fix ((invD 1).mul_mem hc hc) (hS3 s hs t ht)
    · have hs' := hSD s hs
      have ht' := hSD t ht
      have hm : s⁻¹ * t⁻¹ * s * t ∈ invD 1 :=
        (invD 1).mul_mem ((invD 1).mul_mem ((invD 1).mul_mem ((invD 1).inv_mem hs')
          ((invD 1).inv_mem ht')) hs') ht'
      have h1 := eq_one_of_fix hm (hS4 s hs t ht (by rw [hs2]; exact fix_one)
        (by rw [ht2]; exact fix_one))
      calc s * t = t * s * (s⁻¹ * t⁻¹ * s * t) := by group
        _ = t * s := by rw [h1, mul_one]
    · have hsub : {s | s ∈ S ∧ s * s = 1} ⊆ {s | s ∈ S ∧ Fix3 (n := 1782) (by norm_num) (s * s)} :=
        fun s hs => ⟨hs.1, by rw [hs.2]; exact fix_one⟩
      exact le_trans (Set.ncard_le_ncard hsub) hS5
  refine ⟨fun k hk => (hw k hk).2.2, hcard, hzR, hwR, hp, mem_M hcan hHP hms, hhc, S, hSF, ?_⟩
  intro τ hτ hcomm
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := decomp hτ
  have hf1 := fixOK_sound k_fix1 (k := 5) (by decide) hGNe hcomm (b := 1) (by norm_num)
  have hf2 := fixOK_sound k_fix2 (k := 5) (by decide) hGNe hcomm (b := 2) (by norm_num)
  have hlev : ∀ i < 3, ∀ a < rcnt (SuzInvF1.LR i),
      PR (trK 1782 (1782 * 11) SuzInvF1.LR SuzInvF1.TR i a) (TT i a) ∧
      PR (triK 1782 (1782 * 11) SuzInvF1.LR SuzInvF1.TRI i a) (TT i a)⁻¹ :=
    fun i hi a ha => (lev_facts hi ha).2
  have h1728 : rcnt (SuzInvF1.LR 0) = 1728 := Nat.eq_of_beq_eq_true k_lr0
  have hcs : ∀ lo len, centK 1782 11 SuzInvF1.LR SuzInvF1.TR SuzInvF1.TRI GN 5 SV F1 F2 lo len =
      true → lo ≤ a → a < lo + len →
      code3 ((TT 0 a * TT 1 b * TT 2 c) ⟨0, by norm_num⟩) ((TT 0 a * TT 1 b * TT 2 c) ⟨1, by norm_num⟩)
        ((TT 0 a * TT 1 b * TT 2 c) ⟨2, by norm_num⟩) ∈ SV :=
    fun lo len hc' hlo hlen => centK_sound (by norm_num) TT hlev k_chain hc' hGNe ha hb hc hlo hlen
      hcomm hf1 hf2
  have hcode : code3 ((TT 0 a * TT 1 b * TT 2 c) ⟨0, by norm_num⟩)
      ((TT 0 a * TT 1 b * TT 2 c) ⟨1, by norm_num⟩) ((TT 0 a * TT 1 b * TT 2 c) ⟨2, by norm_num⟩) ∈
      SV := by
    rcases (by omega : a < 432 ∨ (432 ≤ a ∧ a < 864) ∨ (864 ≤ a ∧ a < 1296) ∨
      (1296 ≤ a ∧ a < 1728)) with h | h | h | h
    · exact hcs 0 432 k_cent0 (by omega) (by omega)
    · exact hcs 432 432 k_cent1 (by omega) (by omega)
    · exact hcs 864 432 k_cent2 (by omega) (by omega)
    · exact hcs 1296 432 k_cent3 (by omega) (by omega)
  obtain ⟨s, hs, hsc⟩ := hS1 _ hcode
  have hsD := hSD s hs
  obtain ⟨e0, e1, e2⟩ := code3_inj (by omega) (by omega) (by omega) (by omega) hsc
  have hfix : Fix3 (n := 1782) (by norm_num) (s⁻¹ * (TT 0 a * TT 1 b * TT 2 c)) := by
    intro i hi
    have key : ∀ x : Fin 1782, (s x : Nat) = ((TT 0 a * TT 1 b * TT 2 c) x : Nat) →
        ((s⁻¹ * (TT 0 a * TT 1 b * TT 2 c)) x : Nat) = x := by
      intro x hx
      rw [Equiv.Perm.mul_apply, ← Fin.ext hx]
      simp
    interval_cases i
    · exact key _ e0
    · exact key _ e1
    · exact key _ e2
  have h1 := eq_one_of_fix ((invD 1).mul_mem ((invD 1).inv_mem hsD) hτ) hfix
  have e : TT 0 a * TT 1 b * TT 2 c = s := by
    calc TT 0 a * TT 1 b * TT 2 c = s * (s⁻¹ * (TT 0 a * TT 1 b * TT 2 c)) := by group
      _ = s := by rw [h1, mul_one]
  rw [e]
  exact hs

end Glue

end CertificateChecks.KernelSpor.N27216

end
