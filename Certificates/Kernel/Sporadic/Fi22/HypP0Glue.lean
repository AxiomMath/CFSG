module

public import Certificates.Kernel.Sporadic.Fi22.HypP0
public import Certificates.Kernel.Sporadic.Fi22.HypR1Glue
public import CFSG.Certificates.Kernel.Spor.CommBaseFSound

public section

namespace CertificateChecks.KernelSpor.Fi22P0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

variable {g₁ g₂ t : Equiv.Perm (Fin 3510)}

@[expose] def gp (g₁ g₂ : Equiv.Perm (Fin 3510)) (j : ℕ) : Equiv.Perm (Fin 3510) :=
  [g₁, g₂, g₁⁻¹, g₂⁻¹].getD j 1

@[expose] def hval (g₁ g₂ : Equiv.Perm (Fin 3510)) (s : List ℕ × ℕ) : Equiv.Perm (Fin 3510) :=
  word (gp g₁ g₂) s.1 ^ s.2

@[expose] def letterP (g₁ g₂ t : Equiv.Perm (Fin 3510)) (S : List (List ℕ × ℕ)) (z : ℕ) :
    Equiv.Perm (Fin 3510) :=
  if z < S.length then hval g₁ g₂ (S.getD z ([], 0))
  else if z = S.length then t else (hval g₁ g₂ (S.getD (z - (S.length + 1)) ([], 0)))⁻¹

@[expose] def Sset (K : Subgroup (Equiv.Perm (Fin 3510))) (g₁ g₂ : Equiv.Perm (Fin 3510))
    (S : List (List ℕ × ℕ)) (nA : ℕ) : Set K :=
  {k | ∃ i < nA, ((k : Equiv.Perm (Fin 3510)) = hval g₁ g₂ (S.getD i ([], 0)) ∨
    (k : Equiv.Perm (Fin 3510)) = (hval g₁ g₂ (S.getD i ([], 0)))⁻¹)}

theorem strictN_eqP (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eqP (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem prep_c {P Q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g)
    (hQ : PRep 3510 12 Q h) : PRep 3510 12 (Fi22X.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_one : PRep 3510 12 one 1 := prep_pidn (by norm_num) (by norm_num)

theorem commute_of_commOK {P Q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g)
    (hQ : PRep 3510 12 Q h) (e : commOK P Q = true) : Commute g h := by
  rw [commOK, Nat.beq_eq] at e
  refine prep_unique (prep_c hP hQ) ?_
  rw [e]
  exact prep_c hQ hP

theorem eq_one_of_ppow {P : ℕ} {g : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g) {e : ℕ}
    (h : ppow P e = one) (hp : ∀ e, PRep 3510 12 (ppow P e) (g ^ e)) : g ^ e = 1 := by
  have h1 := hp e
  rw [h] at h1
  exact prep_unique h1 prep_one

theorem prep_ppow {P : ℕ} {g : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g) :
    ∀ e, PRep 3510 12 (ppow P e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact prep_one
  | e + 1 => by
    have e1 : ppow P (e + 1) = Fi22X.c P (ppow P e) := strictN_eqP _ _
    rw [e1, pow_succ']
    exact prep_c hP (prep_ppow hP e)

theorem prep_wval {g : ℕ → ℕ} (hG : ∀ j < 4, PRep 3510 12 (g j) (gp g₁ g₂ j)) :
    ∀ {W : List ℕ}, (∀ z ∈ W, z < 4) → PRep 3510 12 (wval g W) (word (gp g₁ g₂) W)
  | [], _ => prep_one
  | z :: W, h => by
    have ih := prep_wval hG (W := W) fun y hy => h y (List.mem_cons_of_mem z hy)
    have e1 : wval g (z :: W) = Fi22X.c (g z) (wval g W) := strictN_eqP _ _
    rw [e1, word, List.map_cons, List.prod_cons]
    exact prep_c (hG z (h z List.mem_cons_self)) ih

theorem prep_wpow {g : ℕ → ℕ} (hG : ∀ j < 4, PRep 3510 12 (g j) (gp g₁ g₂ j))
    {s : List ℕ × ℕ} (hs : ∀ z ∈ s.1, z < 4) : PRep 3510 12 (wpow g s) (hval g₁ g₂ s) := by
  rw [wpow, strictN_eqP]
  exact prep_ppow (prep_wval hG hs) s.2

theorem specsOK_eq {M g : ℕ → ℕ} :
    ∀ {S : List (List ℕ × ℕ)} {i : ℕ}, specsOK M g S i = true →
      ∀ k (hk : k < S.length), M (i + k) = wpow g S[k]
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | s :: S, i, h, k, hk => by
    change bAnd(Nat.beq (M i) (wpow g s), specsOK M g S (Nat.succ i)) = true at h
    rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    rcases k with _ | k
    · exact h.1
    · have := specsOK_eq h.2 k (by simpa using hk)
      rw [List.getElem_cons_succ, ← this]
      congr 1
      omega

theorem prep_lettersOK {M g : ℕ → ℕ} {T nA E : ℕ} {S : List (List ℕ × ℕ)}
    (hG : ∀ j < 4, PRep 3510 12 (g j) (gp g₁ g₂ j)) (ht : PRep 3510 12 T t)
    (hS : ∀ s ∈ S, ∀ z ∈ s.1, z < 4) (h : lettersOK M g T nA E S = true) :
    (∀ z < 2 * S.length + 1, PRep 3510 12 (M z) (letterP g₁ g₂ t S z)) ∧
      ∀ i, nA ≤ i → i < S.length → (S.getD i ([], 0)).2 = E := by
  rw [lettersOK, strictB_eqP] at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, allN_iff, allL_iff, Nat.add_eq] at h
  obtain ⟨-, hm, hinv, hE, hsp⟩ := h
  have hsp' := specsOK_eq hsp
  have hh : ∀ i (hi : i < S.length), PRep 3510 12 (M i) (hval g₁ g₂ (S.getD i ([], 0))) := by
    intro i hi
    have e := hsp' i hi
    rw [Nat.zero_add] at e
    rw [e, List.getD_eq_getElem _ _ hi]
    exact prep_wpow hG (hS _ (List.getElem_mem hi))
  refine ⟨fun z hz => ?_, fun i hi1 hi2 => ?_⟩
  · unfold letterP
    split_ifs with h1 h2
    · exact hh z h1
    · rw [h2, hm]
      exact ht
    · have hi : z - (S.length + 1) < S.length := by omega
      have := prep_inv_of_permOK (hh _ hi) (hinv _ hi)
      rwa [show S.length + 1 + (z - (S.length + 1)) = z by omega] at this
  · rw [List.getD_eq_getElem _ _ hi2]
    have hmem : S[i] ∈ S.drop nA := by
      rw [List.mem_iff_getElem]
      exact ⟨i - nA, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩
    exact hE _ hmem

theorem word_mem {K : Subgroup (Equiv.Perm (Fin 3510))} (hgK : ∀ j < 4, gp g₁ g₂ j ∈ K)
    {W : List ℕ} (hW : ∀ z ∈ W, z < 4) : word (gp g₁ g₂) W ∈ K := by
  refine K.list_prod_mem fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact hgK z (hW z hz)

theorem letterIn_of {K : Subgroup (Equiv.Perm (Fin 3510))} {nA E : ℕ} {S : List (List ℕ × ℕ)}
    (hgK : ∀ j < 4, gp g₁ g₂ j ∈ K) (htK : ∀ k ∈ K, Commute k t)
    (hS : ∀ s ∈ S, ∀ z ∈ s.1, z < 4) (hE : ∀ i, nA ≤ i → i < S.length → (S.getD i ([], 0)).2 = E) :
    ∀ z < 2 * S.length + 1, LetterIn K (Sset K g₁ g₂ S nA) E (letterP g₁ g₂ t S z) := by
  intro z hz
  have hW : ∀ i, (∀ y ∈ (S.getD i ([], 0)).1, y < 4) := by
    intro i y hy
    by_cases hi : i < S.length
    · rw [List.getD_eq_getElem _ _ hi] at hy
      exact hS _ (List.getElem_mem hi) y hy
    · rw [List.getD_eq_default _ _ (by omega)] at hy
      exact absurd hy List.not_mem_nil
  have hmem : ∀ i, hval g₁ g₂ (S.getD i ([], 0)) ∈ K := fun i =>
    K.pow_mem (word_mem hgK (hW i)) _
  have hpow : ∀ i, nA ≤ i → i < S.length →
      hval g₁ g₂ (S.getD i ([], 0)) = (((⟨_, word_mem hgK (hW i)⟩ : K) ^ E : K) :
        Equiv.Perm (Fin 3510)) := by
    intro i h1 h2
    rw [Subgroup.coe_pow, hval, hE i h1 h2]
  unfold letterP
  split_ifs with h1 h2
  · by_cases hA : z < nA
    · exact Or.inl ⟨⟨_, hmem z⟩, ⟨z, hA, Or.inl rfl⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨_, (hpow z (by omega) h1).symm⟩)
  · exact Or.inr (Or.inr fun k => htK k k.2)
  · set i := z - (S.length + 1)
    by_cases hA : i < nA
    · exact Or.inl ⟨⟨_, K.inv_mem (hmem i)⟩, ⟨i, hA, Or.inr rfl⟩, rfl⟩
    · refine Or.inr (Or.inl ⟨(⟨_, word_mem hgK (hW i)⟩ : K)⁻¹, ?_⟩)
      rw [inv_pow, Subgroup.coe_inv, ← hpow i (by omega) (by omega)]

theorem commute_val_iff {K : Subgroup (Equiv.Perm (Fin 3510))} {a b : K}
    (h : Commute (a : Equiv.Perm (Fin 3510)) b) : Commute a b :=
  Subtype.ext h.eq

theorem pow_val {K : Subgroup (Equiv.Perm (Fin 3510))} {a : K} {e : ℕ}
    (h : (a : Equiv.Perm (Fin 3510)) ^ e = 1) : a ^ e = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])

theorem prep_T : PRep 3510 12 T (fi22ExtRep 0) := by
  have h := rep_fi22ExtRep (k := 0) (by norm_num)
  rw [Fi22E2067.ext_eq (L := 21 + 0) (by norm_num)] at h
  exact prep_of_rep h

theorem fourClassesLarge_C0
    (H : Subgroup (Equiv.Perm (Fin 3510))) (hPH : fi22P ≤ H) :
    FourClassesLarge ↥(centralizerIn H (fi22ExtRep 0)) := by
  have hg := gensAll
  simp only [gensOK, bAnd_eq, Bool.and_eq_true, allN_iff] at hg
  obtain ⟨hcn, -, hp02, hp13, -, s0, s1, c0, c1⟩ := hg
  obtain ⟨g₁, m1, h1⟩ := Fi22R1.exists_mem_P (hcn 0 (by norm_num)) hp02 s0
  obtain ⟨g₂, m2, h2⟩ := Fi22R1.exists_mem_P (hcn 1 (by norm_num)) hp13 s1
  have ht := prep_T
  set K := centralizerIn H (fi22ExtRep 0)
  have hG : ∀ j < 4, PRep 3510 12 (G j) (gp g₁ g₂ j) := by
    intro j hj
    interval_cases j
    · exact h1
    · exact h2
    · exact prep_inv_of_permOK h1 hp02
    · exact prep_inv_of_permOK h2 hp13
  have k1 : g₁ ∈ K := mem_centralizerIn.2 ⟨hPH m1, (commute_of_commOK h1 ht c0).eq⟩
  have k2 : g₂ ∈ K := mem_centralizerIn.2 ⟨hPH m2, (commute_of_commOK h2 ht c1).eq⟩
  have hgK : ∀ j < 4, gp g₁ g₂ j ∈ K := by
    intro j hj
    interval_cases j
    · exact k1
    · exact k2
    · exact K.inv_mem k1
    · exact K.inv_mem k2
  have htK : ∀ k ∈ K, Commute k (fi22ExtRep 0) := fun k hk => (mem_centralizerIn.1 hk).2
  have hSA : ∀ s ∈ Fi22P0aD.S, ∀ z ∈ s.1, z < 4 := by decide +kernel
  have hSB : ∀ s ∈ Fi22P0bD.S, ∀ z ∈ s.1, z < 4 := by decide +kernel
  have lA : Fi22P0aD.S.length = 9 := by decide +kernel
  have lB : Fi22P0bD.S.length = 8 := by decide +kernel
  obtain ⟨pA, eA⟩ := prep_lettersOK hG ht hSA lettersA
  obtain ⟨pB, eB⟩ := prep_lettersOK hG ht hSB lettersB
  rw [lA] at pA
  rw [lB] at pB
  have hA := caseA
  simp only [aOK, bAnd_eq, Bool.and_eq_true, allN_iff, Nat.beq_eq] at hA
  obtain ⟨a3, a01, a02, a12⟩ := hA
  have hpA : ∀ i < 3, PRep 3510 12 (LA i) (hval g₁ g₂ (Fi22P0aD.S.getD i ([], 0))) := by
    intro i hi
    have := pA i (by omega)
    unfold letterP at this
    rwa [if_pos (by rw [lA]; omega)] at this
  have hcA : ∀ i < 3, ∀ j < 3, Commute (hval g₁ g₂ (Fi22P0aD.S.getD i ([], 0)))
      (hval g₁ g₂ (Fi22P0aD.S.getD j ([], 0))) := by
    have c01 := commute_of_commOK (hpA 0 (by norm_num)) (hpA 1 (by norm_num)) a01
    have c02 := commute_of_commOK (hpA 0 (by norm_num)) (hpA 2 (by norm_num)) a02
    have c12 := commute_of_commOK (hpA 1 (by norm_num)) (hpA 2 (by norm_num)) a12
    intro i hi j hj
    interval_cases i <;> interval_cases j
    · exact Commute.refl _
    · exact c01
    · exact c02
    · exact c01.symm
    · exact Commute.refl _
    · exact c12
    · exact c02.symm
    · exact c12.symm
    · exact Commute.refl _
  have hSA3 : ∀ a ∈ Sset K g₁ g₂ Fi22P0aD.S 3, ∀ b ∈ Sset K g₁ g₂ Fi22P0aD.S 3, Commute a b := by
    rintro a ⟨i, hi, ha⟩ b ⟨j, hj, hb⟩
    refine commute_val_iff ?_
    have c := hcA i hi j hj
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
    · exact c
    · exact c.inv_right
    · exact c.inv_left
    · exact c.inv_inv
  have hSA3' : ∀ a ∈ Sset K g₁ g₂ Fi22P0aD.S 3, a ^ 3 = 1 := by
    rintro a ⟨i, hi, ha⟩
    have e := eq_one_of_ppow (hpA i hi) (a3 i hi) (prep_ppow (hpA i hi))
    refine pow_val ?_
    rcases ha with ha | ha <;> rw [ha]
    · exact e
    · rw [inv_pow, e, inv_one]
  have hB := caseB
  simp only [bOK, bAnd_eq, Bool.and_eq_true, allL_iff, Nat.beq_eq] at hB
  obtain ⟨b16, bW⟩ := hB
  have g16 : g₁ ^ 16 = 1 := eq_one_of_ppow h1 b16 (prep_ppow h1)
  have hZ : ∀ i < 2, hval g₁ g₂ (Fi22P0bD.S.getD i ([], 0)) ∈ Subgroup.zpowers g₁ := by
    intro i hi
    have hiS : i < Fi22P0bD.S.length := by omega
    rw [List.getD_eq_getElem _ _ hiS]
    have hmem : Fi22P0bD.S[i] ∈ Fi22P0bD.S.take 2 :=
      List.mem_iff_getElem.2 ⟨i, by simp; omega, by rw [List.getElem_take]⟩
    have hw := bW _ hmem
    refine Subgroup.pow_mem _ ((Subgroup.zpowers g₁).list_prod_mem fun x hx => ?_) _
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    have := hw z hz
    rw [bIf_eqC] at this
    split_ifs at this with h0
    · rw [Nat.eq_of_beq_eq_true h0]
      exact Subgroup.mem_zpowers g₁
    · rw [Nat.eq_of_beq_eq_true this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers g₁)
  have hSBz : ∀ a ∈ Sset K g₁ g₂ Fi22P0bD.S 2, (a : Equiv.Perm (Fin 3510)) ∈ Subgroup.zpowers g₁ := by
    rintro a ⟨i, hi, ha | ha⟩ <;> rw [ha]
    · exact hZ i hi
    · exact Subgroup.inv_mem _ (hZ i hi)
  have hSB2 : ∀ a ∈ Sset K g₁ g₂ Fi22P0bD.S 2, ∀ b ∈ Sset K g₁ g₂ Fi22P0bD.S 2, Commute a b := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hSBz a ha)
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 (hSBz b hb)
    refine commute_val_iff ?_
    rw [← hk, ← hl]
    exact Commute.zpow_zpow_self g₁ k l
  have hSB16 : ∀ a ∈ Sset K g₁ g₂ Fi22P0bD.S 2, a ^ 16 = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hSBz a ha)
    refine pow_val ?_
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, g16, one_zpow]
  have iA := letterIn_of (K := K) hgK htK hSA eA
  have iB := letterIn_of (K := K) hgK htK hSB eB
  rw [lA] at iA
  rw [lB] at iB
  exact fourClassesLarge_of_commBaseF K hSA3 hSA3' hSB2 hSB16 pA iA pB iB baseA baseB

end CertificateChecks.KernelSpor.Fi22P0

end
