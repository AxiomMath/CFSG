module

public import CFSG.Certificates.Kernel.MonsterB.QFormSound
public import Certificates.Kernel.MonsterB.Coset3023Sound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.Coset3023

open CFSG.KC.KDense CFSG.KLie.CT CFSG.Monster.B CFSG.KC.SortTree CFSG.KC.Bfs
  CFSG.Monster.B.TwoA.Census

theorem pack_xor {x1 y1 x2 y2 : ℕ} (h1 : x1 < 2 ^ 12) (h2 : x2 < 2 ^ 12) :
    (x1 + 2 ^ 12 * y1) ^^^ (x2 + 2 ^ 12 * y2) = (x1 ^^^ x2) + 2 ^ 12 * (y1 ^^^ y2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.add_comm x1, Nat.add_comm x2, Nat.add_comm (x1 ^^^ x2), Nat.testBit_xor,
    Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow h1 h2)]
  split <;> simp [Nat.testBit_xor]

theorem enc_low (x : Model.Pauli) :
    Rep4371.Native.CosetEnum.enc x % 2 ^ 24 = x.2.1 % 2 ^ 12 + 2 ^ 12 * (x.2.2 % 2 ^ 12) := by
  unfold Rep4371.Native.CosetEnum.enc
  have h1 := Nat.mod_lt x.2.1 (show 0 < 2 ^ 12 by norm_num)
  have h2 := Nat.mod_lt x.2.2 (show 0 < 2 ^ 12 by norm_num)
  split <;> omega

theorem enc_lt (x : Model.Pauli) : Rep4371.Native.CosetEnum.enc x < 2 ^ 25 := by
  unfold Rep4371.Native.CosetEnum.enc
  have h1 := Nat.mod_lt x.2.1 (show 0 < 2 ^ 12 by norm_num)
  have h2 := Nat.mod_lt x.2.2 (show 0 < 2 ^ 12 by norm_num)
  split <;> omega

theorem act_lt (G : Array Model.Pauli) (k n : ℕ) : Rep4371.Native.CosetEnum.act G k n < 2 ^ 25 :=
  enc_lt _

theorem act_low (G : Array Model.Pauli) (k n : ℕ) :
    Rep4371.Native.CosetEnum.act G k n % 2 ^ 24 =
      n % 2 ^ 24 ^^^ Rep4371.Native.CosetEnum.act G k 0 % 2 ^ 24 := by
  unfold Rep4371.Native.CosetEnum.act
  rw [enc_low, enc_low]
  simp only [Rep4371.Native.Pauli.mul, Rep4371.Native.CosetEnum.dec, Rep4371.Native.CosetEnum.inv,
    Rep4371.Native.Pauli.a, Rep4371.Native.Pauli.d, Rep4371.Native.Pauli.s, Nat.zero_mod,
    Nat.zero_div]
  have hn : n % 2 ^ 24 = n % 2 ^ 12 + 2 ^ 12 * (n / 2 ^ 12 % 2 ^ 12) := by omega
  rw [hn, pack_xor (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  congr 1
  · simp only [Nat.xor_mod_two_pow, Nat.mod_mod, -Nat.reducePow]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_xor]
    cases (G[k]!.2.1 % 2 ^ 12).testBit j <;> cases (n % 2 ^ 12).testBit j <;>
      cases ((Rep4371.Native.CosetEnum.gen k).2.1 % 2 ^ 12).testBit j <;> simp
  · congr 1
    simp only [Nat.xor_mod_two_pow, Nat.mod_mod, -Nat.reducePow]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_xor]
    cases (G[k]!.2.2 % 2 ^ 12).testBit j <;> cases (n / 2 ^ 12 % 2 ^ 12).testBit j <;>
      cases ((Rep4371.Native.CosetEnum.gen k).2.2 % 2 ^ 12).testBit j <;> simp

theorem comb_xor (B n m m' : ℕ) : comb B n (m ^^^ m') = comb B n m ^^^ comb B n m' := by
  unfold comb
  rw [← CFSG.KC.QForm.xorK_xor]
  congr 1
  funext j
  rw [CFSG.KC.U6Orb.bit_eq, CFSG.KC.U6Orb.bit_eq, CFSG.KC.U6Orb.bit_eq, Nat.testBit_xor]
  cases m.testBit j <;> cases m'.testBit j <;> simp

theorem comb_zero (B n : ℕ) : comb B n 0 = 0 := by
  unfold comb
  exact CFSG.KC.QForm.xorK_zero fun t _ => by rw [CFSG.KC.U6Orb.bit_eq]; simp

theorem spanOK_spec {act : ℕ → ℕ → ℕ} {B C n : ℕ} (h : spanOK act B C n = true) :
    ∀ k < 24, fget C k 12 < 2 ^ n ∧ comb B n (fget C k 12) = act k 0 % 2 ^ 24 := by
  intro k hk
  have := (allN_iff' _ _).1 h k hk
  rw [andB_iff, Nat.blt_eq, Nat.beq_eq, pw2_eq'] at this
  refine ⟨this.1, ?_⟩
  rw [this.2]
  exact Nat.and_two_pow_sub_one_eq_mod _ 24

theorem reach_span {G : Array Model.Pauli} {B C n root : ℕ}
    (h : spanOK (Rep4371.Native.CosetEnum.act G) B C n = true) {x : ℕ}
    (hx : Reach (Rep4371.Native.CosetEnum.act G) 24 root x) :
    ∃ m < 2 ^ n, x % 2 ^ 24 = root % 2 ^ 24 ^^^ comb B n m := by
  have hs := spanOK_spec h
  induction hx with
  | root => exact ⟨0, by positivity, by rw [comb_zero, Nat.xor_zero]⟩
  | step k hk _ ih =>
    obtain ⟨m, hm, e⟩ := ih
    obtain ⟨hc, ec⟩ := hs k hk
    refine ⟨m ^^^ fget C k 12, Nat.xor_lt_two_pow hm hc, ?_⟩
    rw [act_low, e, ← ec, comb_xor, Nat.xor_assoc]

theorem card_reach_le {G : Array Model.Pauli} {B C n root : ℕ}
    (h : spanOK (Rep4371.Native.CosetEnum.act G) B C n = true) (hroot : root < 2 ^ 25)
    (S : Finset ℕ) (hS : ∀ x ∈ S, Reach (Rep4371.Native.CosetEnum.act G) 24 root x) :
    S.card ≤ 2 * 2 ^ n := by
  have hsub : S ⊆ (Finset.range 2 ×ˢ Finset.range (2 ^ n)).image
      fun p => 2 ^ 24 * p.1 + (root % 2 ^ 24 ^^^ comb B n p.2) := by
    intro x hx
    have hr := hS x hx
    obtain ⟨m, hm, e⟩ := reach_span h hr
    have hlt : x < 2 ^ 25 := by
      cases hr with
      | root => exact hroot
      | step k _ _ => exact act_lt G k _
    refine Finset.mem_image.2 ⟨(x / 2 ^ 24, m), Finset.mem_product.2
      ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 hm⟩, ?_⟩
    dsimp only
    rw [← e]
    omega
  calc S.card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.range 2 ×ˢ Finset.range (2 ^ n)).card := Finset.card_image_le
    _ = 2 * 2 ^ n := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

theorem valF_lt (r : ℕ) : valF 25 r < 2 ^ 25 := by
  change Nat.land r (maskN 25) < 2 ^ 25
  unfold maskN pw2
  change r &&& ((1 <<< 25) - 1) < 2 ^ 25
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

@[expose] def ClassSpec (act : ℕ → ℕ → ℕ) (root n : ℕ) (rec : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  (∀ x, Reach act 24 root x ↔ x ∈ S) ∧ S.card = n ∧ (∀ x ∈ S, root ≤ x ∧ x < 2 ^ 25) ∧
    ∀ i < n, valF 25 (rec i) ∈ S

theorem class_big {G : Array Model.Pauli} {root n wp Cc B C dim : ℕ} {rec : ℕ → ℕ}
    (hT : treeOK (Rep4371.Native.CosetEnum.act G) 24 (fun _ => true) root rec n 25 4 wp 64 Cc = true)
    (h0 : valF 25 (rec 0) = root) (hsp : spanOK (Rep4371.Native.CosetEnum.act G) B C dim = true)
    (hn : n = 2 * 2 ^ dim) :
    ∃ S, ClassSpec (Rep4371.Native.CosetEnum.act G) root n rec S := by
  obtain ⟨hr, -, hlt, -⟩ := tree_sound hT
  have hroot : root < 2 ^ 25 := h0 ▸ valF_lt _
  let S := (Finset.range n).image fun i => valF 25 (rec i)
  have hmem : ∀ x, x ∈ S ↔ ∃ i < n, valF 25 (rec i) = x := fun x => by simp [S]
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact absurd e (ne_of_lt (hlt a b hab hb))
    · rfl
    · exact absurd e (ne_of_gt (hlt b a hab ha))
  have hSr : ∀ x ∈ S, Reach (Rep4371.Native.CosetEnum.act G) 24 root x := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    exact hr i hi
  refine ⟨S, fun x => ⟨fun hx => ?_, hSr x⟩, hcard, fun x hx => ?_, fun i hi => (hmem _).2 ⟨i, hi, rfl⟩⟩
  · by_contra hnot
    have := card_reach_le hsp hroot (insert x S) fun y hy => by
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx
      · exact hSr y hy
    rw [Finset.card_insert_of_notMem hnot, hcard] at this
    omega
  · obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    refine ⟨?_, valF_lt _⟩
    rcases Nat.eq_zero_or_pos i with rfl | h
    · rw [h0]
    · exact h0 ▸ le_of_lt (hlt 0 i h hi)

theorem class_small {act : ℕ → ℕ → ℕ} {root n wp Cc : ℕ} {rec : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    (hT : treeOK act 24 (fun _ => true) root rec n 25 4 wp 64 Cc = true)
    (h0 : valF 25 (rec 0) = root) (hE : closeOK act 24 rec E n 25 64 4 = true) (hn : 0 < n) :
    ∃ S, ClassSpec act root n rec S := by
  obtain ⟨S, hS, hc, -, hge, hmem⟩ := orbit_sound hn hT hE
  refine ⟨S, hS, hc, fun x hx => ⟨h0 ▸ hge x hx, ?_⟩, fun i hi => (hmem _).2 ⟨i, hi, rfl⟩⟩
  obtain ⟨i, -, rfl⟩ := (hmem x).1 hx
  exact valF_lt _

theorem natBfs_class {act : ℕ → ℕ → ℕ} {root n : ℕ} {rec : ℕ → ℕ} {S : Finset ℕ}
    (hS : ClassSpec act root n rec S) (hn : n ≤ 9000) :
    natCertOK act 24 (fun x => decide (x < 2 ^ 25)) root (natBfs act 24 root 9000) = true ∧
      (natBfs act 24 root 9000).pts.size = n ∧
      (∀ j < (natBfs act 24 root 9000).pts.size, root ≤ (natBfs act 24 root 9000).pts[j]!) ∧
      ∀ i < n, valF 25 (rec i) ∈ (natBfs act 24 root 9000).pts := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  obtain ⟨c1, c2, c3, -⟩ := natBfs_spec (valid := fun x => decide (x < 2 ^ 25)) (fuel := 9000) S h1
    (fun x hx => decide_eq_true (h3 x hx).2) (h2 ▸ hn)
  refine ⟨c1, c3.trans h2, fun j hj => ?_, fun i hi => (c2 _).2 (h4 i hi)⟩
  rw [getElem!_pos _ j hj]
  exact (h3 _ ((c2 _).1 (Array.getElem_mem hj))).1

end CertificateChecks.Coset3023

end
