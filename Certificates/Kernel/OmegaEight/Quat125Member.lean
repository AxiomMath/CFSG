module

public import Certificates.Kernel.OmegaEight.Quat125IdentC
public import Certificates.Kernel.OmegaEight.Quat125KM
public import Certificates.Kernel.OmegaEight.E4O8MembersGlue
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8Inputs
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import Certificates.Kernel.OmegaEight.Roots127Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.PCent CFSG.KC.Misc.ArrEnum

theorem q125m_bitK (m p : Nat) : bitK m p = m.testBit p := by
  unfold bitK
  change Nat.blt 0 (m &&& 1 <<< p) = _
  rw [Nat.one_shiftLeft, q125_and_two_pow]
  cases e : m.testBit p
  · first | rfl | (simp only [Bool.false_eq_true, if_false]; rfl)
  · simp [Nat.blt_eq, Nat.two_pow_pos]

theorem q125m_ai (X : Equiv.Perm (Fin 360)) (p : Fin 360) : X (X⁻¹ p) = p := X.apply_symm_apply p

theorem q125m_ia (X : Equiv.Perm (Fin 360)) (p : Fin 360) : X⁻¹ (X p) = p := X.symm_apply_apply p

theorem q125m_card_conj (g : Equiv.Perm (Fin 360)) (K : Subgroup (Equiv.Perm (Fin 360))) :
    Nat.card (conjSub g K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem q125m_dsw1_eq (m d A : Nat) :
    dsw1 m d A = m ^^^ ((((m >>> d) ^^^ m) &&& A) ^^^ ((((m >>> d) ^^^ m) &&& A) <<< d)) := by
  unfold dsw1
  rw [q125sN]
  rfl

theorem q125m_dsw1_xor (a b d A : Nat) : dsw1 (a ^^^ b) d A = dsw1 a d A ^^^ dsw1 b d A := by
  have ht : ((((a ^^^ b) >>> d) ^^^ (a ^^^ b)) &&& A) =
      (((a >>> d) ^^^ a) &&& A) ^^^ (((b >>> d) ^^^ b) &&& A) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight]
    cases a.testBit (d + i) <;> cases b.testBit (d + i) <;> cases a.testBit i <;>
      cases b.testBit i <;> cases A.testBit i <;> rfl
  rw [q125m_dsw1_eq, q125m_dsw1_eq, q125m_dsw1_eq, ht, Nat.shiftLeft_xor_distrib]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;>
    cases (((a >>> d) ^^^ a) &&& A).testBit i <;> cases (((b >>> d) ^^^ b) &&& A).testBit i <;>
    cases ((((a >>> d) ^^^ a) &&& A) <<< d).testBit i <;>
    cases ((((b >>> d) ^^^ b) &&& A) <<< d).testBit i <;> rfl

theorem q125m_dswK_cons (d A : Nat) (t : List (Nat × Nat)) (m : Nat) :
    dswK ((d, A) :: t) m = dswK t (dsw1 m d A) := by
  change strictN (dsw1 m d A) (dswK t) = _
  rw [q125sN]

theorem q125m_dswK_xor : ∀ (sw : List (Nat × Nat)) (a b : Nat),
    dswK sw (a ^^^ b) = dswK sw a ^^^ dswK sw b
  | [], _, _ => rfl
  | (d, A) :: t, a, b => by
    rw [q125m_dswK_cons, q125m_dswK_cons, q125m_dswK_cons, q125m_dsw1_xor, q125m_dswK_xor t]

theorem q125m_dswK_zero (sw : List (Nat × Nat)) : dswK sw 0 = 0 := by
  have h := q125m_dswK_xor sw 0 0
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem q125m_dswK_bits {sw : List (Nat × Nat)} {X : Nat → Nat}
    (hX : ∀ a < 240, dswK sw (1 <<< a) = 1 <<< X a)
    (hinj : ∀ a < 240, ∀ b < 240, X a = X b → a = b) :
    ∀ n ≤ 240, ∀ m < 2 ^ n, ∀ q,
      ((dswK sw m).testBit q = true ↔ ∃ a < n, m.testBit a = true ∧ X a = q) := by
  intro n
  induction n with
  | zero =>
    intro _ m hm q
    have hm0 : m = 0 := by omega
    subst hm0
    rw [q125m_dswK_zero, Nat.zero_testBit]
    simp
  | succ n ih =>
    intro hn m hm q
    have hr : m % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
    have hrb : ∀ a < n, (m % 2 ^ n).testBit a = m.testBit a := fun a ha => by
      rw [Nat.testBit_mod_two_pow]
      simp [ha]
    have hrhi : ∀ a, n ≤ a → (m % 2 ^ n).testBit a = false := fun a ha => by
      rw [Nat.testBit_mod_two_pow]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left
      omega
    have hmhi : ∀ a, n < a → m.testBit a = false := fun a ha =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) ha))
    have ih' := ih (by omega) _ hr q
    cases hb : m.testBit n with
    | false =>
      have e : m = m % 2 ^ n := by
        apply Nat.eq_of_testBit_eq
        intro a
        rcases Nat.lt_trichotomy a n with h | h | h
        · rw [hrb a h]
        · subst h
          rw [hb, hrhi _ le_rfl]
        · rw [hmhi a h, hrhi a (by omega)]
      have hd : dswK sw m = dswK sw (m % 2 ^ n) := by
        conv_lhs => rw [e]
      rw [hd, ih']
      constructor
      · rintro ⟨a, ha, hab, hxa⟩
        exact ⟨a, by omega, by rw [← hrb a ha]; exact hab, hxa⟩
      · rintro ⟨a, ha, hab, hxa⟩
        have han : a ≠ n := fun h => by
          rw [h, hb] at hab
          exact Bool.noConfusion hab
        exact ⟨a, by omega, by rw [hrb a (by omega)]; exact hab, hxa⟩
    | true =>
      have e : m = m % 2 ^ n ^^^ 1 <<< n := by
        apply Nat.eq_of_testBit_eq
        intro a
        rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
        rcases Nat.lt_trichotomy a n with h | h | h
        · rw [hrb a h]
          simp [Nat.ne_of_gt h]
        · subst h
          rw [hb, hrhi _ le_rfl]
          simp
        · rw [hmhi a h, hrhi a (by omega)]
          simp [Nat.ne_of_lt h]
      have hd : dswK sw m = dswK sw (m % 2 ^ n) ^^^ 1 <<< X n := by
        conv_lhs => rw [e]
        rw [q125m_dswK_xor, hX n (by omega)]
      rw [hd, Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hq : X n = q
      · have hf : (dswK sw (m % 2 ^ n)).testBit q = false := by
          cases h : (dswK sw (m % 2 ^ n)).testBit q
          · rfl
          · obtain ⟨a, ha, -, hxa⟩ := ih'.1 h
            exact absurd (hinj a (by omega) n (by omega) (hxa.trans hq.symm)) (by omega)
        rw [hf, decide_eq_true hq]
        exact ⟨fun _ => ⟨n, by omega, hb, hq⟩, fun _ => rfl⟩
      · rw [decide_eq_false hq, Bool.xor_false, ih']
        constructor
        · rintro ⟨a, ha, hab, hxa⟩
          exact ⟨a, by omega, by rw [← hrb a ha]; exact hab, hxa⟩
        · rintro ⟨a, ha, hab, hxa⟩
          have han : a ≠ n := fun h => hq (h ▸ hxa)
          exact ⟨a, by omega, by rw [hrb a (by omega)]; exact hab, hxa⟩

@[expose] noncomputable def q125mSwR (G : Nat → Nat) (SW : List (List (Nat × Nat))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun r => Nat.beq r (nat_lit 8))
    (fun sw _ ih r => strictB (G r) fun X => bAnd(allN (nat_lit 240) (fun a =>
      strictB (pg (nat_lit 9) (nat_lit 511) X a) fun x => bAnd(Nat.blt x (nat_lit 240),
        Nat.beq (dswK sw (Nat.shiftLeft (nat_lit 1) a)) (Nat.shiftLeft (nat_lit 1) x))),
      ih (Nat.succ r))) SW

theorem q125m_swTie (G : Nat → Nat) (SW : List (List (Nat × Nat))) :
    swTie G SW = q125mSwR G SW 0 := rfl

theorem q125m_swR_cons (G : Nat → Nat) (sw : List (Nat × Nat)) (t : List (List (Nat × Nat)))
    (r : Nat) : q125mSwR G (sw :: t) r = strictB (G r) fun X => bAnd(allN (nat_lit 240) (fun a =>
      strictB (pg (nat_lit 9) (nat_lit 511) X a) fun x => bAnd(Nat.blt x (nat_lit 240),
        Nat.beq (dswK sw (Nat.shiftLeft (nat_lit 1) a)) (Nat.shiftLeft (nat_lit 1) x))),
      q125mSwR G t (Nat.succ r)) := rfl

theorem q125m_swR_spec (G : Nat → Nat) : ∀ (SW : List (List (Nat × Nat))) (r0 : Nat),
    q125mSwR G SW r0 = true → r0 + SW.length = 8 ∧ ∀ i < SW.length, ∀ a < 240,
      pg 9 511 (G (r0 + i)) a < 240 ∧
        dswK (SW.getD i []) (1 <<< a) = 1 <<< pg 9 511 (G (r0 + i)) a
  | [], r0, h => ⟨by have := Nat.eq_of_beq_eq_true h; simpa using this,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | sw :: t, r0, h => by
    rw [q125m_swR_cons, q125sB, q125bAnd] at h
    obtain ⟨ha, ht⟩ := h
    obtain ⟨hl, hi⟩ := q125m_swR_spec G t (r0 + 1) ht
    refine ⟨by simp only [List.length_cons]; omega, fun i hi' a ha' => ?_⟩
    cases i with
    | zero =>
      have h1 := CFSG.KC.Pack.allN_spec ha a ha'
      beta_reduce at h1
      rw [q125sB, q125bAnd] at h1
      exact ⟨q125blt.1 h1.1, Nat.eq_of_beq_eq_true h1.2⟩
    | succ i =>
      have := hi i (by simp only [List.length_cons] at hi'; omega) a ha'
      have e : r0 + 1 + i = r0 + (i + 1) := by omega
      rw [e] at this
      simpa only [List.getD_cons_succ] using this

theorem q125m_swAtK (m : Nat) : ∀ (SW : List (List (Nat × Nat))) (l : Nat), l < SW.length →
    swAtK SW l m = dswK (SW.getD l []) m
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | sw :: t, l + 1, h => by
    have e : swAtK (sw :: t) (l + 1) m =
        Bool.rec (motive := fun _ => Nat) (swAtK t (Nat.sub (l + 1) 1) m) (dswK sw m)
          (Nat.beq (l + 1) 0) := rfl
    have e2 : Nat.sub (l + 1) 1 = l := Nat.add_sub_cancel l 1
    rw [e, q125nIfF (q125beqF (by omega)), e2, List.getD_cons_succ]
    exact q125m_swAtK m t l (by simp only [List.length_cons] at h; omega)

theorem q125m_mask9 : mask 9 = 511 := rfl

theorem q125m_PP_S {r : Nat} (hr : r < 8) : CFSG.KC.BfsPin.PP 360 9 (AP.S r) :=
  E4C.e4c_pp (root_facts hr).2.2.1

theorem q125m_S_apply {r : Nat} (hr : r < 8) (a : Fin 360) :
    ((toPerm 360 9 (AP.S r) a : Fin 360) : Nat) = pg 9 511 (AP.S r) a := by
  rw [toPerm_apply (q125m_PP_S hr), q125m_mask9]

theorem q125m_swaps_len : swaps.length = 8 := by
  have h := (q125m_swR_spec _ swaps 0 (by rw [← q125m_swTie]; exact kSwap125)).1
  omega

theorem q125m_inv_lt {X : Equiv.Perm (Fin 360)} (hX : ∀ a : Fin 360, (a : Nat) < 240 → (X a : Nat) < 240)
    (p : Fin 360) : ((X⁻¹ p : Fin 360) : Nat) < 240 ↔ (p : Nat) < 240 := by
  classical
  constructor
  · intro h
    have := hX _ h
    rwa [q125m_ai] at this
  · intro hp
    set S : Finset (Fin 360) := Finset.univ.filter fun a => (a : Nat) < 240
    have hsub : S.image X ⊆ S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hX y hy
    have heq : S.image X = S :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ X.injective])
    have hpS : p ∈ S.image X := by
      rw [heq]
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hpS
    rw [q125m_ia]
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hy

theorem q125m_swap {r : Nat} (hr : r < 8) :
    (∀ a : Fin 360, (a : Nat) < 240 → ((toPerm 360 9 (AP.S r) a : Fin 360) : Nat) < 240) ∧
    ∀ m < 2 ^ 240, ∀ p : Fin 360, ((dswK (swaps.getD r []) m).testBit p = true ↔
      m.testBit ((toPerm 360 9 (AP.S r))⁻¹ p) = true) := by
  have hs := (q125m_swR_spec _ swaps 0 (by rw [← q125m_swTie]; exact kSwap125)).2 r
    (by rw [q125m_swaps_len]; exact hr)
  simp only [Nat.zero_add] at hs
  set X := toPerm 360 9 (AP.S r)
  have h1 : ∀ a : Fin 360, (a : Nat) < 240 → ((X a : Fin 360) : Nat) < 240 := fun a ha => by
    rw [q125m_S_apply hr]
    exact (hs a ha).1
  refine ⟨h1, fun m hm p => ?_⟩
  have hinj : ∀ a < 240, ∀ b < 240, pg 9 511 (AP.S r) a = pg 9 511 (AP.S r) b → a = b := by
    intro a ha b hb e
    have e' : X ⟨a, by omega⟩ = X ⟨b, by omega⟩ := by
      apply Fin.ext
      rw [q125m_S_apply hr, q125m_S_apply hr]
      exact e
    exact congrArg Fin.val (X.injective e')
  rw [q125m_dswK_bits (fun a ha => (hs a ha).2) hinj 240 le_rfl m hm p]
  constructor
  · rintro ⟨a, ha, hab, hxa⟩
    have e : X ⟨a, by omega⟩ = p := by
      apply Fin.ext
      rw [q125m_S_apply hr]
      exact hxa
    rw [← e, q125m_ia]
    exact hab
  · intro hb
    have ha : ((X⁻¹ p : Fin 360) : Nat) < 240 := by
      by_contra hn
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at hb
      exact Bool.noConfusion hb
    refine ⟨_, ha, hb, ?_⟩
    have := q125m_S_apply hr (X⁻¹ p)
    rw [q125m_ai] at this
    exact this.symm

theorem q125m_allBlk {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ i, b ≤ i → i < b + len → f i = true
  | 0, _, i, h1, h2 => absurd h2 (by omega)
  | len + 1, h, i, h1, h2 => by
    have e : allBlk b f (len + 1) = bAnd(f (Nat.add b len), allBlk b f len) := rfl
    rw [e, q125bAnd] at h
    by_cases hi : i = b + len
    · subst hi
      exact h.1
    · exact q125m_allBlk h.2 i h1 (by omega)

#kc_forall_tree q125mRowsAll (fun s => q125Mem s = true) 13 CertificateChecks.KernelO8.Q125.ch125m

theorem q125m_row {k : Nat} (hk : k < 6300) :
    memRowK RT MT swaps (fixMK e4U om0V 240) (mainK 0) k = true ∧ sortAt RT MT k = true := by
  have h13 : k / 512 < 13 := by omega
  have h := q125mRowsAll (k / 512) h13
  unfold q125Mem at h
  rw [q125sB] at h
  have h' := q125m_allBlk h k (Nat.mul_div_le k 512) (by
    change k < 512 * (k / 512) + 512
    omega)
  beta_reduce at h'
  rw [q125bIfT (q125blt.2 hk), q125bAnd] at h'
  exact h'

theorem q125m_rowW_lt (r : Nat) : rowW r < 2 ^ 80 := by
  unfold rowW
  have := Nat.and_le_right (n := r) (m := 1208925819614629174706175)
  change r &&& 1208925819614629174706175 ≤ _ at this
  change r &&& 1208925819614629174706175 < _
  omega

theorem q125m_tree {k : Nat} (hk : k < 6300) :
    (k = 0 → rowW (RT 0) = 0 ∧ MT 0 = fixMK e4U om0V 240) ∧
    (k ≠ 0 → rowP (RT k) < 6300 ∧ 0 < rowW (RT k) % 16 ∧ rowW (RT k) % 16 < 9 ∧
      rowW (RT (rowP (RT k))) = rowW (RT k) / 16 ∧
      MT k = swAtK swaps (rowW (RT k) % 16 - 1) (MT (rowP (RT k)))) := by
  have h := (q125m_row hk).1
  unfold memRowK at h
  simp only [q125sB] at h
  have h1 := (q125bAnd.1 h).1
  have e15 : ∀ w : Nat, Nat.land w 15 = w % 16 := fun w => Nat.and_two_pow_sub_one_eq_mod w 4
  have e4 : ∀ w : Nat, Nat.shiftRight w 4 = w / 16 := fun w => Nat.shiftRight_eq_div_pow w 4
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  · subst hk0
    rw [q125bIfT (q125beqT rfl), q125bAnd] at h1
    exact ⟨Nat.eq_of_beq_eq_true h1.1, Nat.eq_of_beq_eq_true h1.2⟩
  · rw [q125bIfF (q125beqF hk0)] at h1
    simp only [q125bAnd, Nat.blt_eq] at h1
    obtain ⟨hp, hl0, hl9, hw, hm⟩ := h1
    have hw' := Nat.eq_of_beq_eq_true hw
    have hm' := Nat.eq_of_beq_eq_true hm
    rw [e15] at hl0 hl9 hm'
    rw [e4] at hw'
    exact ⟨hp, hl0, hl9, hw', hm'⟩

theorem q125m_MT_lt {k : Nat} (hk : k < 6300) : MT k < 2 ^ 240 := by
  have h := CFSG.KC.Pack.allN_spec kMB125 k hk
  rw [Nat.blt_eq] at h
  change MT k < 1 <<< 240 at h
  rw [Nat.one_shiftLeft] at h
  exact h

theorem q125m_M0 (p : Fin 360) : (fixMK e4U om0V 240).testBit p = true ↔
    (p : Nat) < 240 ∧ toPerm 360 9 e4U p = p ∧ toPerm 360 9 om0V p = p := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := E4C.e4c_pm
  have hu : ∀ q : Fin 360, toPerm 360 9 e4U q = q ↔ pg 9 511 e4U q = q := fun q => by
    rw [Fin.ext_iff, toPerm_apply hpu, q125m_mask9]
  have hv : ∀ q : Fin 360, toPerm 360 9 om0V q = q ↔ pg 9 511 om0V q = q := fun q => by
    rw [Fin.ext_iff, toPerm_apply hpv, q125m_mask9]
  rw [hu, hv]
  by_cases hp : (p : Nat) < 240
  · have hk := kFixM125
    rw [q125sB] at hk
    have h := CFSG.KC.Pack.allN_spec hk p hp
    beta_reduce at h
    rw [q125m_bitK] at h
    have hb := Nat.eq_of_beq_eq_true h
    have key : (fixMK e4U om0V 240).testBit p =
        bAnd(Nat.beq (pg 9 511 e4U p) p, Nat.beq (pg 9 511 om0V p) p) := by
      revert hb
      cases (fixMK e4U om0V 240).testBit p <;>
        cases bAnd(Nat.beq (pg 9 511 e4U p) p, Nat.beq (pg 9 511 om0V p) p) <;> intro hb <;>
        first | rfl | exact absurd hb (by decide)
    rw [key, q125bAnd]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hp, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨q125beqT h1, q125beqT h2⟩
  · have h0 := (q125m_tree (k := 0) (by norm_num)).1 rfl
    rw [← h0.2, Nat.testBit_lt_two_pow (lt_of_lt_of_le (q125m_MT_lt (k := 0) (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hp]

section Word

variable (P : Nat → Equiv.Perm (Fin 360)) (hP0 : P 0 = 1)
  (hPs : ∀ l W, 0 < l → l < 9 → W < 2 ^ 76 → P (l + 16 * W) = toPerm 360 9 (AP.S (l - 1)) * P W)
include hP0 hPs

theorem q125_mask : ∀ W, ∀ k < 6300, rowW (RT k) = W →
    P W ∈ omegaT ∧ ∀ p : Fin 360, ((MT k).testBit p = true ↔ (p : Nat) < 240 ∧
      toPerm 360 9 e4U ((P W)⁻¹ p) = (P W)⁻¹ p ∧ toPerm 360 9 om0V ((P W)⁻¹ p) = (P W)⁻¹ p) := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
    intro k hk hW
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨hw0, hm0⟩ := (q125m_tree hk).1 rfl
      rw [← hW, hw0, hP0]
      refine ⟨omegaT.one_mem, fun p => ?_⟩
      rw [inv_one, Equiv.Perm.one_apply, hm0]
      exact q125m_M0 p
    · obtain ⟨hp, hl0, hl9, hwp, hm⟩ := (q125m_tree hk).2 hk0
      rw [hW] at hl0 hl9 hwp hm
      have hWlt : W < 2 ^ 80 := hW ▸ q125m_rowW_lt _
      have hsplit : W = W % 16 + 16 * (W / 16) := (Nat.mod_add_div W 16).symm
      have hPW : P W = toPerm 360 9 (AP.S (W % 16 - 1)) * P (W / 16) := by
        conv_lhs => rw [hsplit]
        exact hPs _ _ hl0 hl9 (by omega)
      obtain ⟨ihm, ihb⟩ := ih (W / 16) (by omega) _ hp hwp
      have hr : W % 16 - 1 < 8 := by omega
      obtain ⟨hX, hsw⟩ := q125m_swap hr
      refine ⟨by rw [hPW]; exact omegaT.mul_mem ((E4C.e4c_omegaT) ▸
        gen_mem (G := AP.S) (ngen := 8) hr) ihm, fun p => ?_⟩
      rw [hm, q125m_swAtK _ _ _ (by rw [q125m_swaps_len]; exact hr),
        hsw _ (q125m_MT_lt hp) p, ihb, q125m_inv_lt hX, hPW, mul_inv_rev, Equiv.Perm.mul_apply]

end Word

theorem q125m_fix_conj (g : Equiv.Perm (Fin 360)) (p : Fin 360) :
    (toPerm 360 9 e4U (g⁻¹ p) = g⁻¹ p ∧ toPerm 360 9 om0V (g⁻¹ p) = g⁻¹ p) ↔
      ∀ x ∈ conjSub g q125K0, x p = p := by
  constructor
  · rintro ⟨hu, hv⟩ x hx
    rw [mem_conjSub_iff] at hx
    have hle : q125K0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 360)) (g⁻¹ p) := by
      rw [q125K0, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hu
      · exact hv
    have h := hle hx
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, q125m_ai] at h
    exact g⁻¹.injective h
  · intro h
    have hu : toPerm 360 9 e4U ∈ q125K0 := Subgroup.subset_closure (Set.mem_insert _ _)
    have hv : toPerm 360 9 om0V ∈ q125K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have h1 := h _ (conj_mem_conjSub hu)
    have h2 := h _ (conj_mem_conjSub hv)
    simp only [Equiv.Perm.mul_apply] at h1 h2
    exact ⟨g.injective (h1.trans (q125m_ai g p).symm), g.injective (h2.trans (q125m_ai g p).symm)⟩

theorem q125m_sort {i : Nat} (hi : i < 6300) : rowS (RT i) < 6300 ∧
    (i < 6299 → MT (rowS (RT i)) < MT (rowS (RT (i + 1)))) := by
  have h := (q125m_row hi).2
  unfold sortAt at h
  rw [q125sB, q125bAnd] at h
  refine ⟨q125blt.1 h.1, fun hi' => ?_⟩
  rw [q125bIfT (q125blt.2 hi')] at h
  exact q125blt.1 h.2

theorem q125m_sort_lt : ∀ j < 6300, ∀ i < j, MT (rowS (RT i)) < MT (rowS (RT j)) := by
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    have h := (q125m_sort (i := j) (by omega)).2 (by omega)
    rcases Nat.lt_or_ge i j with h' | h'
    · exact (ih (by omega) i h').trans h
    · have : i = j := by omega
      subst this
      exact h

theorem q125m_MT_inj {i j : Nat} (hi : i < 6300) (hj : j < 6300) (e : MT i = MT j) : i = j := by
  let f : Fin 6300 → Fin 6300 := fun a => ⟨rowS (RT a), (q125m_sort a.2).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e1 : rowS (RT a) = rowS (RT b) := congrArg Fin.val hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · have := q125m_sort_lt b b.2 a h
      rw [e1] at this
      exact lt_irrefl _ this
    · have := q125m_sort_lt a a.2 b h
      rw [e1] at this
      exact lt_irrefl _ this
  have hs := Finite.injective_iff_surjective.1 hf
  obtain ⟨a, ha⟩ := hs ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hs ⟨j, hj⟩
  have ea : rowS (RT a) = i := congrArg Fin.val ha
  have eb : rowS (RT b) = j := congrArg Fin.val hb
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := q125m_sort_lt b b.2 a h
    rw [ea, eb, e] at this
    exact absurd this (lt_irrefl _)
  · rw [← ea, ← eb, Fin.ext h]
  · have := q125m_sort_lt a a.2 b h
    rw [ea, eb, e] at this
    exact absurd this (lt_irrefl _)

section Distinct

variable (P : Nat → Equiv.Perm (Fin 360)) (hP0 : P 0 = 1)
  (hPs : ∀ l W, 0 < l → l < 9 → W < 2 ^ 76 → P (l + 16 * W) = toPerm 360 9 (AP.S (l - 1)) * P W)
include hP0 hPs

theorem q125_rows_distinct {i j : Nat} (hi : i < 6300)
    (hj : j < 6300) (e : conjSub (P (rowW (RT i))) q125K0 = conjSub (P (rowW (RT j))) q125K0) :
    i = j := by
  apply q125m_MT_inj hi hj
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < 360
  · have h1 := (q125_mask P hP0 hPs _ i hi rfl).2 ⟨q, hq⟩
    have h2 := (q125_mask P hP0 hPs _ j hj rfl).2 ⟨q, hq⟩
    rw [q125m_fix_conj, e, ← q125m_fix_conj] at h1
    rw [Bool.eq_iff_iff]
    exact h1.trans h2.symm
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (q125m_MT_lt hi)
        (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (q125m_MT_lt hj)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end Distinct

@[expose] noncomputable def q125Ls : List (Subgroup (Equiv.Perm (Fin 360))) :=
  [q125K0, conjSub (toPerm 360 9 (wO (q125MW 1))) q125K0,
    conjSub (toPerm 360 9 (wO (q125MW 3))) q125K0, conjSub (toPerm 360 9 (wO (q125MW 4))) q125K0]

section Lists


theorem q125m_e4L : ∀ P ∈ e4L, CFSG.KC.BfsPin.PP 360 9 P ∧ toPerm 360 9 P ∈ q125K0 := by
  obtain ⟨-, -, -, -, -, hpx, hpu, hpv⟩ := E4C.e4c_pm
  intro P hP
  refine ⟨?_, q125_mem_K0 (List.any_eq_true.2 ⟨P, hP, Nat.beq_refl P⟩)⟩
  simp only [e4L, e4Q, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CFSG.KC.BfsPin.PP.id E4C.ch550106sz
  · exact hpx
  · exact hpu
  · exact hpu.mul hpx
  · exact hpv
  · exact hpv.mul hpx
  · exact hpu.mul hpv
  · exact (hpu.mul hpv).mul hpx

theorem q125m_PL {j : Nat} (hj : j < 4) :
    (∀ y ∈ q125PL.getD j [], CFSG.KC.BfsPin.PP 360 9 y ∧ toPerm 360 9 y ∈ q125Ls.getD j ⊥) ∧
    q125Ls.getD j ⊥ = Subgroup.closure {toPerm 360 9 ((q125PL.getD j []).getD 2 0),
      toPerm 360 9 ((q125PL.getD j []).getD 4 0)} ∧
    (q125PL.getD j []).length = 8 ∧ Nat.card (q125Ls.getD j ⊥) = Nat.card q125K0 := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := E4C.e4c_pm
  have hw : ∀ w : Nat, CFSG.KC.BfsPin.PP 360 9 w →
      (∀ y ∈ e4L.map (cjI w (pinv w)), CFSG.KC.BfsPin.PP 360 9 y ∧
        toPerm 360 9 y ∈ conjSub (toPerm 360 9 w) q125K0) ∧
      conjSub (toPerm 360 9 w) q125K0 = Subgroup.closure {toPerm 360 9 (cj w e4U),
        toPerm 360 9 (cj w om0V)} := by
    intro w hpw
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      refine ⟨q125_PP_cj hpw (q125m_e4L x hx).1, ?_⟩
      change toPerm 360 9 (cj w x) ∈ _
      rw [q125_toPerm_cj hpw (q125m_e4L x hx).1]
      exact conj_mem_conjSub (q125m_e4L x hx).2
    · rw [q125_conj_K0, q125_toPerm_cj hpw hpu, q125_toPerm_cj hpw hpv]
  have hc : ∀ g, Nat.card (conjSub g q125K0) = Nat.card q125K0 := fun g =>
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · exact ⟨fun y hy => q125m_e4L y hy, rfl, rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hw _ (E4C.e4c_pp (by decide +kernel : permB 360 9 (wO (q125MW 1)) = true))
    exact ⟨h1, h2, rfl, hc _⟩
  · obtain ⟨h1, h2⟩ := hw _ (E4C.e4c_pp (by decide +kernel : permB 360 9 (wO (q125MW 3)) = true))
    exact ⟨h1, h2, rfl, hc _⟩
  · obtain ⟨h1, h2⟩ := hw _ (E4C.e4c_pp (by decide +kernel : permB 360 9 (wO (q125MW 4)) = true))
    exact ⟨h1, h2, rfl, hc _⟩

theorem q125m_g0_eq {l : Nat} (hl : l < 3) :
    E4C.g0K l = wO (CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [Int.ofNat (l + 1)]) := by
  have hg := E4C.ch550106g0
  simp only [bAnd_iff] at hg
  obtain ⟨e0, e1, e2, -, -⟩ := hg
  interval_cases l
  · exact Nat.eq_of_beq_eq_true e0
  · exact Nat.eq_of_beq_eq_true e1
  · exact Nat.eq_of_beq_eq_true e2

theorem q125m_mem_getD {α : Type} {l : List α} {d : α} {j : Nat} (h : j < l.length) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem q125m_g0_maps {l : Nat} (hl : l < 3) :
    ∀ L ∈ q125Ls, conjSub (toPerm 360 9 (E4C.g0K l)) L ∈ q125Ls := by
  intro L hL
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  have hj4 : j < 4 := hj
  rw [← List.getD_eq_getElem _ ⊥ hj]
  have h := kLists125
  simp only [q125bAnd] at h
  have h' := CFSG.KC.Pack.allN_spec h.2.2.2 l hl
  beta_reduce at h'
  rw [q125sB, q125sB, ← q125m_g0_eq hl] at h'
  have h'' := CFSG.KC.Pack.allN_spec h' j hj4
  beta_reduce at h''
  rw [q125sB, q125bAnd] at h''
  obtain ⟨hj', hall⟩ := h''
  set j' := (g0perm.getD l []).getD j 0
  have hj'4 : j' < 4 := q125blt.1 hj'
  obtain ⟨hF1, hF2, hlen, hcard⟩ := q125m_PL hj4
  obtain ⟨hG1, -, -, hcard'⟩ := q125m_PL hj'4
  have hpg := E4C.e4c_pm.1 l (by omega)
  have key : ∀ e < 8, toPerm 360 9 (E4C.g0K l) * toPerm 360 9 ((q125PL.getD j []).getD e 0) *
      (toPerm 360 9 (E4C.g0K l))⁻¹ ∈ q125Ls.getD j' ⊥ := by
    intro e he
    have hmem : (q125PL.getD j []).getD e 0 ∈ q125PL.getD j [] :=
      q125m_mem_getD (by rw [hlen]; exact he)
    have hx := List.all_eq_true.1 hall _ hmem
    unfold e4Mem at hx
    obtain ⟨y, hy, hye⟩ := List.any_eq_true.1 hx
    rw [← q125_toPerm_cj hpg (hF1 _ hmem).1]
    change toPerm 360 9 (cjI (E4C.g0K l) (pinv (E4C.g0K l)) _) ∈ _
    rw [Nat.eq_of_beq_eq_true hye]
    exact (hG1 y hy).2
  have hle : conjSub (toPerm 360 9 (E4C.g0K l)) (q125Ls.getD j ⊥) ≤ q125Ls.getD j' ⊥ := by
    rw [hF2]
    unfold conjSub
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact key 2 (by norm_num)
    · exact key 4 (by norm_num)
  have heq : conjSub (toPerm 360 9 (E4C.g0K l)) (q125Ls.getD j ⊥) = q125Ls.getD j' ⊥ :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcard', q125m_card_conj, hcard])
  rw [heq]
  exact q125m_mem_getD hj'4

@[expose] noncomputable def q125N : Subgroup (Equiv.Perm (Fin 360)) :=
  E4C.e4H0 ⊓ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360)))

theorem q125_card_N : 27648 ≤ Nat.card q125N := by
  have hu0 := E4C.ch550106u
  simp only [bAnd_iff] at hu0
  have hu := hu0.1
  unfold classK at hu
  rw [Bool.and_eq_true] at hu
  have hpm := E4C.e4c_pm.1
  have hinv : ∀ j < 3, E4C.g0K (j + 3) = pinvS 360 9 (mask 9) (E4C.g0K j) := by
    intro j hj
    have e := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec hu.1 j (by omega))
    have hm : Nat.mod (Nat.add j (nat_lit 3)) (nat_lit 6) = j + 3 := by
      change (j + 3) % 6 = j + 3
      omega
    have e' : E4C.gi0K j = E4C.g0K (j + 3) := congrArg E4C.g0K hm
    rw [← e', e]
  have hS : ∀ s ∈ gens 360 9 E4C.g0K 6, ∀ L ∈ q125Ls, conjSub s L ∈ q125Ls := by
    rintro _ ⟨k, hk, rfl⟩
    by_cases hk3 : k < 3
    · exact q125m_g0_maps hk3
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rw [hinv j (by omega), toPerm_inv (hpm j (by omega))]
      exact CFSG.KC.O8Quat.conj_mem_inv (q125m_g0_maps (by omega))
  have hL : ∀ h ∈ E4C.e4H0, conjSub h q125K0 ∈ q125Ls := fun h hh =>
    CFSG.KC.O8Quat.conj_mem_of_closure hS hh _ List.mem_cons_self
  have hN : ∀ h ∈ E4C.e4H0, conjSub h q125K0 = q125K0 → h ∈ q125N := fun h hh e =>
    Subgroup.mem_inf.2 ⟨hh, CFSG.ClassicalInvolution.Asc77.mem_normalizer_iff_conjSub_eq.2 e⟩
  have hb := CFSG.KC.O8Quat.card_le_of_conj_mem q125Ls hL hN
  rw [E4C.e4c_H0.2] at hb
  change 110592 ≤ 4 * Nat.card q125N at hb
  omega

end Lists

section Member

variable (P : Nat → Equiv.Perm (Fin 360)) (hP0 : P 0 = 1)
  (hPs : ∀ l W, 0 < l → l < 9 → W < 2 ^ 76 → P (l + 16 * W) = toPerm 360 9 (AP.S (l - 1)) * P W)
include hP0 hPs

theorem q125_member {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) :
    ∃ k < 6300, conjSub g q125K0 = conjSub (P (rowW (RT k))) q125K0 := by
  have hNH : q125N ≤ omegaT := fun x hx => by
    have h := (Subgroup.mem_inf.1 hx).1
    rw [E4C.e4c_H0.1] at h
    exact (Subgroup.mem_inf.1 h).1
  have hNK : ∀ n ∈ q125N, conjSub n q125K0 = q125K0 := fun n hn =>
    CFSG.ClassicalInvolution.Asc77.mem_normalizer_iff_conjSub_eq.1 (Subgroup.mem_inf.1 hn).2
  have hcard : Nat.card omegaT ≤ 6300 * Nat.card q125N := by
    rw [card_omegaT]
    have := q125_card_N
    omega
  exact CFSG.KC.O8Quat.exists_conj_eq_of_card (fun k => P (rowW (RT k)))
    (fun k hk => (q125_mask P hP0 hPs _ k hk rfl).1)
    (fun i hi j hj e => q125_rows_distinct P hP0 hPs hi hj e) hNH hNK hcard hg

end Member

theorem q125m_wO_cons (a : Nat) (r : List Int) :
    wO (Int.ofNat a :: r) = strictN (wO r) (fun T =>
      strictN (CFSG.KS.Mathieu.icode (Int.ofNat a)) (fun c => pcomp 360 9 (mask 9)
        (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
          OmP.S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
          OmP.SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl

section Words

variable (P : Nat → Equiv.Perm (Fin 360)) (hP0 : P 0 = 1)
  (hPs : ∀ l W, 0 < l → l < 9 → W < 2 ^ 76 → P (l + 16 * W) = toPerm 360 9 (AP.S (l - 1)) * P W)
include hP0 hPs

theorem q125m_word : ∀ wd : List Nat, lets8K wd = true → packW wd < 2 ^ 80 →
    CFSG.KC.BfsPin.PP 360 9 (wO (E4O8.toWord wd)) ∧
      toPerm 360 9 (wO (E4O8.toWord wd)) = P (packW wd)
  | [], _, _ => ⟨CFSG.KC.BfsPin.PP.id E4C.ch550106sz, by
      change toPerm 360 9 (pidn 360 9) = P 0
      rw [toPerm_pidn E4C.ch550106sz, hP0]⟩
  | a :: r, h, hlt => by
    have e1 : lets8K (a :: r) = bAnd(Nat.blt 0 a, bAnd(Nat.blt a 9, lets8K r)) := rfl
    rw [e1, q125bAnd, q125bAnd, Nat.blt_eq, Nat.blt_eq] at h
    obtain ⟨ha0, ha9, hr⟩ := h
    have ep : packW (a :: r) = a + 16 * packW r := by
      change a + (packW r <<< 4) = _
      rw [Nat.shiftLeft_eq]
      ring
    rw [ep] at hlt ⊢
    obtain ⟨ihp, ihe⟩ := q125m_word r hr (by omega)
    have ew : wO (E4O8.toWord (a :: r)) = pc (AP.S (a - 1)) (wO (E4O8.toWord r)) := by
      change wO (Int.ofNat a :: E4O8.toWord r) = _
      rw [q125m_wO_cons, q125sN, q125sN]
      have ec : CFSG.KS.Mathieu.icode (Int.ofNat a) = a + a := rfl
      have e0 : Nat.land (a + a) 1 = 0 := by
        change (a + a) &&& 1 = 0
        rw [Nat.and_one_is_mod]
        omega
      rw [ec, q125nIfT (q125beqT e0)]
      have es : Nat.sub (Nat.shiftRight (a + a) 1) 1 = a - 1 := by
        change (a + a) >>> 1 - 1 = a - 1
        rw [Nat.shiftRight_eq_div_pow]
        omega
      rw [es, Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kOmS125 (a - 1) (by omega))]
      rfl
    have hS := q125m_PP_S (r := a - 1) (by omega)
    rw [ew]
    refine ⟨hS.mul ihp, ?_⟩
    change toPerm 360 9 (pcomp 360 9 (mask 9) _ _) = _
    rw [toPerm_mul hS ihp, ihe, hPs a (packW r) ha0 ha9 (by omega)]

omit hP0 hPs in
theorem q125m_rowsLet : ∀ (E : List (List Nat × (Nat × Nat))), rowsLetK E = true →
    ∀ x ∈ E, lets8K x.1 = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | r :: t, h, x, hx => by
    have e : rowsLetK (r :: t) =
        bAnd(Prod.rec (motive := fun _ => Bool) (fun w _ => lets8K w) r, rowsLetK t) := rfl
    rw [e, q125bAnd] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact q125m_rowsLet t h.2 x hx

omit hP0 hPs in
theorem q125m_wTie : ∀ (E : List (List Nat × (Nat × Nat))) (k0 : Nat),
    (List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 6300))
      (fun row _ ih k => bAnd(Prod.rec (motive := fun _ => Bool)
        (fun w _ => Nat.beq (packW w) (rowW (RT k))) row, strictB (Nat.succ k) ih)) E k0) = true →
    k0 + E.length = 6300 ∧ ∀ i < E.length, packW (E.getD i ([], (0, 0))).1 = rowW (RT (k0 + i))
  | [], k0, h => ⟨by have := Nat.eq_of_beq_eq_true h; simpa using this,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | row :: t, k0, h => by
    change bAnd(Nat.beq (packW row.1) (rowW (RT k0)), strictB (Nat.succ k0) _) = true at h
    rw [q125bAnd, q125sB] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hl, hi⟩ := q125m_wTie t (k0 + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi' => ?_⟩
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ i =>
      have := hi i (by simp only [List.length_cons] at hi'; omega)
      have e : k0 + 1 + i = k0 + (i + 1) := by omega
      rw [e] at this
      simpa only [List.getD_cons_succ] using this

theorem q125_wsA : (E4O8.wsA ()).length = 6300 ∧ ∀ k < 6300,
    permOfArr 360 ((E4O8.wsA ()).getD k (idA 360)) = P (rowW (RT k)) := by
  have hw := q125m_wTie e4MR 0 kWTie125
  refine ⟨by rw [wsA_pk, List.length_map, e4WP_length], fun k hk => ?_⟩
  rw [wsA_pk, e4_ws_getD hk]
  have hrf := e4_row_facts (e4_row_at hk)
  rw [← E4C.e4c_toPerm (e4Pm_iff.1 hrf.2.2.1).1]
  have hmem : e4MR.getD k ([], (0, 0)) ∈ e4MR := q125m_mem_getD (by rw [e4_len]; exact hk)
  have hlet := q125m_rowsLet e4MR kWLet125 _ hmem
  have hpk : packW (e4MR.getD k ([], (0, 0))).1 = rowW (RT k) := by
    have := hw.2 k (by rw [e4_len]; exact hk)
    rwa [Nat.zero_add] at this
  have := (q125m_word P hP0 hPs _ hlet (by rw [hpk]; exact q125m_rowW_lt _)).2
  rw [hpk] at this
  exact this

end Words

end CertificateChecks.KernelO8.Q125

end
