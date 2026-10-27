module

public import CFSG.Sporadic.Schreier.PairClasses

public section

namespace CertificateChecks.KernelSporSch.PHSClass

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Sporadic.Schreier.PairNative

theorem conj_mem_of_closed {G : Type*} [Group G] [Finite G] {gs R : Set G}
    (hcl : ∀ g ∈ gs, ∀ y ∈ R, g * y * g⁻¹ ∈ R) :
    ∀ c ∈ Subgroup.closure gs, ∀ y ∈ R, c * y * c⁻¹ ∈ R := by
  have hpow : ∀ c : G, (∀ y ∈ R, c * y * c⁻¹ ∈ R) →
      ∀ k : ℕ, ∀ y ∈ R, c ^ k * y * (c ^ k)⁻¹ ∈ R := by
    intro c hc k
    induction k with
    | zero =>
      intro y hy
      simpa using hy
    | succ k ih =>
      intro y hy
      have h := hc _ (ih y hy)
      have e : c ^ (k + 1) * y * (c ^ (k + 1))⁻¹ = c * (c ^ k * y * (c ^ k)⁻¹) * c⁻¹ := by
        group
      rw [e]
      exact h
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem g hg => exact hcl g hg
  | one =>
    intro y hy
    simpa using hy
  | mul a b _ _ ha hb =>
    intro y hy
    have h := ha _ (hb y hy)
    have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact h
  | inv a _ ha =>
    intro y hy
    have h := hpow a ha (orderOf a - 1) y hy
    have e : a ^ (orderOf a - 1) = a⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos a),
        pow_orderOf_eq_one]
    rw [e] at h
    exact h

variable {n : ℕ}

theorem card_class_of_closed {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) {bs : List ℕ}
    (hH : BaseFaithful Q.originalSubgroup bs) (hbs : ∀ b ∈ bs, b < n)
    {gens gensInv : Array (Array ℕ)} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (hgen : Q.originalSubgroup ≤ Subgroup.closure {g | ∃ l < gens.size, gg l = g})
    {rep : List (Array ℕ)} {x₀ : Equiv.Perm (Fin n)} (hrep : RepW n rep x₀)
    (hx₀ : x₀ ∈ Q.originalSubgroup) {elts : Array (Array ℕ)} {par lab : Array ℕ}
    (hok : closureOK (rawLevels n S base) bs gens gensInv rep elts par lab = true)
    (hcl : ∀ i < elts.size, ∀ l < gens.size, ∃ j < elts.size,
      baseImgs bs (nfWord (rawLevels n S base) elts[j]!) =
        conjImgs bs gens[l]! gensInv[l]! (nfWord (rawLevels n S base) elts[i]!))
    (hd : (elts.toList.map fun nf => imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))).Nodup) :
    Nat.card {y : Q.originalSubgroup // IsConj (⟨x₀, hx₀⟩ : Q.originalSubgroup) y} = elts.size := by
  set P := Q.originalSubgroup
  have hspec := closureOK_spec hA hF hQ hH hbs hg hrep hx₀ hok
  have hpos : 0 < elts.size := by
    simp only [closureOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  have hmem : ∀ k < elts.size, nfElt n S base elts[k]! ∈ P := fun k hk =>
    nfElt_mem hA hF hQ (hspec k hk).1
  set R : Set (Equiv.Perm (Fin n)) := {y | ∃ k < elts.size, nfElt n S base elts[k]! = y}
  have hR : ∀ g ∈ {g | ∃ l < gens.size, gg l = g}, ∀ y ∈ R, g * y * g⁻¹ ∈ R := by
    rintro g ⟨l, hl, rfl⟩ y ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := hcl i hi l hl
    obtain ⟨hgl, hgil, hgP⟩ := hg l hl
    rw [conjImgs_eq] at he
    exact ⟨j, hj, eq_of_baseImgs_eq hH hbs (repW_nfWord hA hF (hspec j hj).1)
      (repW_conj hgl hgil (repW_nfWord hA hF (hspec i hi).1)) (hmem j hj)
      (P.mul_mem (P.mul_mem hgP (hmem i hi)) (P.inv_mem hgP)) he⟩
  have hP : ∀ c ∈ P, ∀ y ∈ R, c * y * c⁻¹ ∈ R := fun c hc =>
    conj_mem_of_closed hR c (hgen hc)
  have hx0R : x₀ ∈ R := by
    obtain ⟨c, hc, hce⟩ := (hspec 0 hpos).2
    have h := hP c⁻¹ (P.inv_mem hc) _ ⟨0, hpos, rfl⟩
    rw [hce] at h
    have e : c⁻¹ * (c * x₀ * c⁻¹) * c⁻¹⁻¹ = x₀ := by group
    rwa [e] at h
  have hkey : ∀ k < elts.size,
      (elts.toList.map fun nf => imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf)))[k]? =
        some (keyElt n bs (nfElt n S base elts[k]!)) := by
    intro k hk
    rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hk, Option.map_some,
      ← getElem!_pos elts k hk, imgKey_baseImgs hbs (repW_nfWord hA hF (hspec k hk).1)]
  let f : Fin elts.size → {y : P // IsConj (⟨x₀, hx₀⟩ : P) y} := fun k =>
    ⟨⟨nfElt n S base elts[k.val]!, hmem k k.2⟩, by
      obtain ⟨c, hc, hce⟩ := (hspec k k.2).2
      exact isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hce.symm)⟩⟩
  have hb : Function.Bijective f := by
    refine ⟨fun i j h => ?_, fun y => ?_⟩
    · have e : nfElt n S base elts[i.val]! = nfElt n S base elts[j.val]! :=
        congrArg (fun y : {y : P // IsConj (⟨x₀, hx₀⟩ : P) y} => ((y : P) : Equiv.Perm (Fin n))) h
      have h1 := hkey i i.2
      have h2 := hkey j j.2
      rw [e, ← h2] at h1
      exact Fin.ext ((List.Nodup.getElem?_inj (i := i.val) (by simp) hd).1 h1)
    · obtain ⟨⟨y, hyP⟩, hy⟩ := y
      obtain ⟨⟨c, hc⟩, hce⟩ := isConj_iff.1 hy
      have hyR := hP c hc x₀ hx0R
      have hyv : c * x₀ * c⁻¹ = y := congrArg Subtype.val hce
      rw [hyv] at hyR
      obtain ⟨k, hk, hke⟩ := hyR
      exact ⟨⟨k, hk⟩, Subtype.ext (Subtype.ext hke)⟩
  rw [← Nat.card_eq_of_bijective f hb, Nat.card_fin]

theorem mul_mem_of_table {G : Type*} [Monoid G] {N k : ℕ} {r : ℕ → G} {gi par lab : ℕ → ℕ}
    {m : ℕ → ℕ → ℕ} (h0 : r 0 = 1)
    (htree : ∀ i < N, 0 < i → par i < i ∧ lab i < k ∧ r i = r (par i) * r (gi (lab i)))
    (hmul : ∀ i < N, ∀ l < k, m i l < N ∧ r i * r (gi l) = r (m i l)) :
    ∀ j < N, ∀ i < N, ∃ t < N, r i * r j = r t := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i hi
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact ⟨i, hi, by rw [h0, mul_one]⟩
    · obtain ⟨hp, hl, he⟩ := htree j hj hpos
      obtain ⟨t, ht, hte⟩ := ih _ hp (hp.trans hj) i hi
      obtain ⟨hm, hme⟩ := hmul t ht (lab j) hl
      exact ⟨m t (lab j), hm, by rw [he, ← mul_assoc, hte, hme]⟩

end CertificateChecks.KernelSporSch.PHSClass

end
