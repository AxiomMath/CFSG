module

public import Certificates.Kernel.SmithD6Lines.Checks
public import Certificates.Kernel.SmithD6T2.Facts
public import Certificates.Kernel.SmithD6Uw.Model

public section

namespace CertificateChecks.SmithD6Lines

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod

theorem lkAll_iff (l : List Nat) : lkAll l = true ↔ ∀ k ∈ l, lkOK k = true := by
  induction l with
  | nil => exact ⟨fun _ k hk => by simp at hk, fun _ => rfl⟩
  | cons k l ih =>
    have e : lkAll (k :: l) = (lkOK k && lkAll l) := rfl
    rw [e, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem lkOK_flatten : ∀ k ∈ J.lineKeysC.flatten, lkOK k = true := by
  intro k hk
  obtain ⟨l, hl, hkl⟩ := List.mem_flatten.1 hk
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
  have hlen : J.lineKeysC.length = 179 := by rw [← lenC_eq, SmithD6Trees.lineKeysC_lenC]
  have h := lineKeys_ok c (lt_of_lt_of_eq hc hlen)
  rw [nthC_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at h
  exact (lkAll_iff _).1 h k hkl

theorem lkOK_spec {k : Nat} (h : lkOK k = true) :
    0 < k / 4096 ∧ k / 4096 < k % 4096 ∧ k % 4096 < (k / 4096) ^^^ (k % 4096) ∧
      (k / 4096) ^^^ (k % 4096) < 4096 ∧ qf (k / 4096) = false ∧ qf (k % 4096) = false ∧
      bf (k / 4096) (k % 4096) = false := by
  simpa only [lkOK, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', and_assoc] using h

theorem bit_eq_zero {b : Bool} (h : bit b = 0) : b = false := by
  cases b
  · rfl
  · simp [bit] at h

theorem bf_symm {x y : Nat} (h : bf x y = false) : bf y x = false := by
  have hB : B12 (dec12 x) (dec12 y) = 0 := by simp [B12_dec12, h, bit]
  refine bit_eq_zero ?_
  rw [← B12_dec12, B12_comm, hB]

theorem ts_xor {a b : Nat} (ha : qf a = false) (hb : qf b = false) (hab : bf a b = false) :
    qf (a ^^^ b) = false ∧ bf a (a ^^^ b) = false ∧ bf b (a ^^^ b) = false := by
  have hqa : q12 (dec12 a) = 0 := by simp [q12_dec12, ha, bit]
  have hqb : q12 (dec12 b) = 0 := by simp [q12_dec12, hb, bit]
  have hB : B12 (dec12 a) (dec12 b) = 0 := by simp [B12_dec12, hab, bit]
  refine ⟨bit_eq_zero ?_, bit_eq_zero ?_, bit_eq_zero ?_⟩
  · rw [← q12_dec12, dec12_xor, q12_add, hqa, hqb, hB, add_zero, add_zero]
  · rw [← B12_dec12, dec12_xor, B12_add_right, B12_self, hB, add_zero]
  · rw [← B12_dec12, dec12_xor, B12_add_right, B12_self, B12_comm, hB, add_zero]

@[expose] def key3 (x y z : Nat) : Nat :=
  4096 * min x (min y z) + (min x (min y z) ^^^ max x (max y z))

theorem key3_eq {x y z x' y' z' : Nat} (h1 : min x (min y z) = min x' (min y' z'))
    (h2 : max x (max y z) = max x' (max y' z')) : key3 x y z = key3 x' y' z' := by
  unfold key3
  rw [h1, h2]

@[irreducible] def pts : Finset Nat := (Finset.range 4096).filter fun x => x ≠ 0 ∧ qf x = false

@[irreducible] def perp (p : Nat) : Finset Nat :=
  (Finset.range 4096).filter fun x => x ≠ 0 ∧ x ≠ p ∧ qf x = false ∧ bf p x = false

@[irreducible] def tsP : Finset (Σ _ : Nat, Nat) := pts.sigma perp

theorem mem_singArr' {x : ℕ} : x ∈ singArr ↔ x < 4096 ∧ x ≠ 0 ∧ qf x = false := by
  simp only [singArr, List.mem_toArray, List.mem_filter, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, Bool.not_eq_true']

@[expose] def kap (s : Σ _ : Nat, Nat) : Nat := key3 s.1 s.2 (s.1 ^^^ s.2)

theorem mem_tsP {a b : Nat} : (⟨a, b⟩ : Σ _ : Nat, Nat) ∈ tsP ↔
    a < 4096 ∧ a ≠ 0 ∧ qf a = false ∧ b < 4096 ∧ b ≠ 0 ∧ b ≠ a ∧ qf b = false ∧
      bf a b = false := by
  simp only [tsP, pts, perp, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, and_assoc]

theorem tsP_card : tsP.card = 2079 * 1054 := by
  have h : ∀ p ∈ pts, (perp p).card = 1054 := fun p hp => by
    simp only [pts, Finset.mem_filter, Finset.mem_range] at hp
    rw [perp]
    exact SmithD6T2.perp_count_codes hp.1 hp.2.1 hp.2.2
  have hp : pts.card = 2079 := by
    rw [pts]
    exact SmithD6T2.pt_count_codes
  rw [tsP, Finset.card_sigma, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, hp]

theorem kap_of_key {k : Nat} (h : lkOK k = true) :
    (⟨k / 4096, k % 4096⟩ : Σ _ : Nat, Nat) ∈ tsP ∧ kap ⟨k / 4096, k % 4096⟩ = k := by
  obtain ⟨h0, h1, h2, h3, hq1, hq2, hb⟩ := lkOK_spec h
  refine ⟨mem_tsP.2 ⟨by omega, by omega, hq1, Nat.mod_lt _ (by norm_num), by omega, by omega,
    hq2, hb⟩, ?_⟩
  have e1 : min (k / 4096) (min (k % 4096) ((k / 4096) ^^^ (k % 4096))) = k / 4096 := by omega
  have e2 : max (k / 4096) (max (k % 4096) ((k / 4096) ^^^ (k % 4096))) =
      (k / 4096) ^^^ (k % 4096) := by omega
  change key3 (k / 4096) (k % 4096) ((k / 4096) ^^^ (k % 4096)) = k
  unfold key3
  rw [e1, e2, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  exact Nat.div_add_mod k 4096

theorem six_le {s : Σ _ : Nat, Nat} (hs : s ∈ tsP) :
    6 ≤ (tsP.filter fun t => kap t = kap s).card := by
  obtain ⟨a, b⟩ := s
  obtain ⟨ha, ha0, hqa, hb, hb0, hba, hqb, hab⟩ := mem_tsP.1 hs
  obtain ⟨hqc, hac, hbc⟩ := ts_xor hqa hqb hab
  have hc : a ^^^ b < 4096 := Nat.xor_lt_two_pow (n := 12) ha hb
  have e1 : a ^^^ (a ^^^ b) = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have e2 : (a ^^^ b) ^^^ b = a := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hca : a ^^^ b ≠ a := fun h => hb0 (by rw [← e1, h, Nat.xor_self])
  have hcb : a ^^^ b ≠ b := fun h => ha0 (by rw [← e2, h, Nat.xor_self])
  have hc0 : a ^^^ b ≠ 0 := fun h => hba (by rw [← e2, h, Nat.zero_xor])
  have e3 : b ^^^ a = a ^^^ b := Nat.xor_comm b a
  have e4 : (a ^^^ b) ^^^ a = b := by rw [Nat.xor_comm, e1]
  have e5 : b ^^^ (a ^^^ b) = a := by rw [Nat.xor_comm, e2]
  have hmem : ∀ x y, x < 4096 → x ≠ 0 → qf x = false → y < 4096 → y ≠ 0 → y ≠ x →
      qf y = false → bf x y = false → (⟨x, y⟩ : Σ _ : Nat, Nat) ∈ tsP :=
    fun x y h1 h2 h3 h4 h5 h6 h7 h8 => mem_tsP.2 ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  let L6 : List (Σ _ : Nat, Nat) :=
    [⟨a, b⟩, ⟨b, a⟩, ⟨a, a ^^^ b⟩, ⟨a ^^^ b, a⟩, ⟨b, a ^^^ b⟩, ⟨a ^^^ b, b⟩]
  have hnd : L6.Nodup := by
    simp [L6, hba, Ne.symm hba, hca, Ne.symm hca, hcb, Ne.symm hcb]
  have hsub : L6.toFinset ⊆ tsP.filter fun t => kap t = kap ⟨a, b⟩ := by
    intro t ht
    simp only [L6, List.mem_toFinset, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at ht
    rw [Finset.mem_filter]
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hs, rfl⟩
    · refine ⟨hmem b a hb hb0 hqb ha ha0 (Ne.symm hba) hqa (bf_symm hab), ?_⟩
      change key3 b a (b ^^^ a) = key3 a b (a ^^^ b)
      rw [e3]
      exact key3_eq (by omega) (by omega)
    · refine ⟨hmem a _ ha ha0 hqa hc hc0 hca hqc hac, ?_⟩
      change key3 a (a ^^^ b) (a ^^^ (a ^^^ b)) = key3 a b (a ^^^ b)
      rw [e1]
      exact key3_eq (by omega) (by omega)
    · refine ⟨hmem _ a hc hc0 hqc ha ha0 (Ne.symm hca) hqa (bf_symm hac), ?_⟩
      change key3 (a ^^^ b) a ((a ^^^ b) ^^^ a) = key3 a b (a ^^^ b)
      rw [e4]
      exact key3_eq (by omega) (by omega)
    · refine ⟨hmem b _ hb hb0 hqb hc hc0 hcb hqc hbc, ?_⟩
      change key3 b (a ^^^ b) (b ^^^ (a ^^^ b)) = key3 a b (a ^^^ b)
      rw [e5]
      exact key3_eq (by omega) (by omega)
    · refine ⟨hmem _ b hc hc0 hqc hb hb0 (Ne.symm hcb) hqb (bf_symm hbc), ?_⟩
      change key3 (a ^^^ b) b ((a ^^^ b) ^^^ b) = key3 a b (a ^^^ b)
      rw [e2]
      exact key3_eq (by omega) (by omega)
  have h6 : L6.toFinset.card = 6 := by rw [List.toFinset_card_of_nodup hnd]; rfl
  rw [← h6]
  exact Finset.card_le_card hsub

theorem card_image_le_of_six {α : Type} [DecidableEq α] (P : Finset α) (f : α → Nat)
    (h6 : ∀ s ∈ P, 6 ≤ (P.filter fun t => f t = f s).card) : 6 * (P.image f).card ≤ P.card := by
  rw [Finset.card_eq_sum_card_image f P]
  calc 6 * (P.image f).card = ∑ _y ∈ P.image f, 6 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun y hy => by
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
        exact h6 t ht

theorem image_card_le : 6 * (tsP.image kap).card ≤ 2079 * 1054 := by
  have h := card_image_le_of_six tsP kap fun s hs => six_le hs
  rw [tsP_card] at h
  exact h

theorem key_mem_of {K : List Nat} (hnd : K.Nodup) (hn : K.length = 365211)
    (hok : ∀ k ∈ K, lkOK k = true) {s : Σ _ : Nat, Nat} (hs : s ∈ tsP) : kap s ∈ K := by
  have hT : K.toFinset.card = 365211 := by rw [List.toFinset_card_of_nodup hnd, hn]
  have hsub : K.toFinset ⊆ tsP.image kap := by
    intro k hk
    obtain ⟨hm, he⟩ := kap_of_key (hok k (List.mem_toFinset.1 hk))
    exact Finset.mem_image.2 ⟨_, hm, he⟩
  have hle : (tsP.image kap).card ≤ K.toFinset.card := by
    have := image_card_le
    omega
  have heq : K.toFinset = tsP.image kap := Finset.eq_of_subset_of_card_le hsub hle
  have hm := Finset.mem_image_of_mem kap hs
  rw [← heq] at hm
  exact List.mem_toFinset.1 hm

theorem key_mem {s : Σ _ : Nat, Nat} (hs : s ∈ tsP) : kap s ∈ J.lineKeysC.flatten := by
  obtain ⟨hp, hn, -, -⟩ := SmithD6Trees.lineKeys_facts
  exact key_mem_of (hp.imp Nat.ne_of_lt) hn lkOK_flatten hs

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
  (hI : ∀ u w, lineIdx u w < 365211 → lineKeys[lineIdx u w]! = 4096 * u + w)
include hK hL hI

theorem lines_of_pinned : (lineKeys.size = 365211 ∧
      ∀ k < 365211, 0 < (linePair k).1 ∧ (linePair k).1 < (linePair k).2 ∧
        (linePair k).2 < ((linePair k).1 ^^^ (linePair k).2) ∧
        ((linePair k).1 ^^^ (linePair k).2) < 4096 ∧ qf (linePair k).1 = false ∧
        qf (linePair k).2 = false ∧ bf (linePair k).1 (linePair k).2 = false ∧
        lineIdx (linePair k).1 (linePair k).2 = k) ∧
    ∀ a ∈ singArr, ∀ b ∈ singArr, a ≠ b → bf a b = false →
      lineIdx3 a b (a ^^^ b) < 365211 := by
  obtain ⟨hp, hn, hf, hs⟩ := SmithD6Trees.lineKeys_facts
  have hnd : J.lineKeysC.flatten.Nodup := hp.imp Nat.ne_of_lt
  refine ⟨⟨by rw [← Array.length_toList, hK, hn], fun k hk => ?_⟩,
    fun a ha b hb hab hbf => ?_⟩
  · have hk' : k < J.lineKeysC.flatten.length := by rw [hn]; exact hk
    have hlp : linePair k =
        (J.lineKeysC.flatten[k] / 4096, J.lineKeysC.flatten[k] % 4096) := by
      unfold linePair
      rw [← Array.getElem!_toList, hK, getElem!_pos J.lineKeysC.flatten k hk']
    rw [hlp]
    obtain ⟨h0, h1, h2, h3, hq1, hq2, hb⟩ :=
      lkOK_spec (lkOK_flatten _ (List.getElem_mem hk'))
    refine ⟨h0, h1, h2, h3, hq1, hq2, hb, ?_⟩
    have hkey : 4096 * (J.lineKeysC.flatten[k] / 4096) + J.lineKeysC.flatten[k] % 4096 =
        J.lineKeysC.flatten[k] := Nat.div_add_mod _ _
    have hm : lineTree.memB (4096 * (J.lineKeysC.flatten[k] / 4096) +
        J.lineKeysC.flatten[k] % 4096) = true := by
      rw [hkey]
      exact (SmithD6Uw.memB_iff_mem hf hs _).2 (List.getElem_mem hk')
    obtain ⟨hlt, -⟩ := hL _ _ (by omega) (Nat.mod_lt _ (by norm_num)) hm
    have hi := hI _ _ hlt
    rw [hkey, ← Array.getElem!_toList, hK,
      getElem!_pos J.lineKeysC.flatten _ (by rw [hn]; exact hlt)] at hi
    exact (hnd.getElem_inj_iff).1 hi
  · rw [mem_singArr'] at ha hb
    have hmem := key_mem (s := ⟨a, b⟩)
      (mem_tsP.2 ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, fun h => hab h.symm, hb.2.2, hbf⟩)
    have ha4 := ha.1
    have hb4 := hb.1
    have hc : a ^^^ b < 4096 := Nat.xor_lt_two_pow (n := 12) ha4 hb4
    have hlo : min a (min b (a ^^^ b)) < 4096 := by omega
    have hhi : max a (max b (a ^^^ b)) < 4096 := by omega
    have hx : min a (min b (a ^^^ b)) ^^^ max a (max b (a ^^^ b)) < 4096 :=
      Nat.xor_lt_two_pow (n := 12) hlo hhi
    exact (hL _ _ hlo hx ((SmithD6Uw.memB_iff_mem hf hs _).2 hmem)).1

end Model

end CertificateChecks.SmithD6Lines

end
