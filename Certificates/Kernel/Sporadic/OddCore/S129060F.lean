module

public import Certificates.Kernel.Sporadic.OddCore.S129060K
public import Certificates.Kernel.Sporadic.Suz.EndK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzEndModel

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S129060

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch CFSG.Sporadic.SuzOddCore
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.RankTwoSporadic.Suz
  CertificateChecks.KernelSpor

@[expose] noncomputable def aP (k : Nat) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (unpack 1782 11 (A k))

theorem strictB_val (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIf_ff {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c <;> revert h <;> decide

theorem bIf_tt {c x : Bool} (h : bIf(c, true, x) = true) : c = true ∨ x = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

theorem ap {P : Nat} {x : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P x) (p : Fin 1782) :
    ((x p : Fin 1782) : ℕ) = fv P p := (h p).symm

theorem ext1782 {x y : Equiv.Perm (Fin 1782)}
    (h : ∀ p : Fin 1782, ((x p : Fin 1782) : ℕ) = y p) : x = y :=
  Equiv.ext fun p => Fin.ext (h p)

theorem pA {k : Nat} (hk : k < 6) : PRep 1782 11 (A k) (aP k) ∧ PRep 1782 11 (AI k) (aP k)⁻¹ := by
  have h := pOK
  unfold pK at h
  exact SuzEnd.prep_of (allN_spec h k hk)

theorem mem_M {k : Nat}
    (hk : k < 6) : aP k ∈ suzM := by
  have h := pOK
  unfold pK at h
  have hm := mOK
  unfold mK at hm
  exact mem_suzM_of (SuzEnd.inMA_of (allN_spec h k hk) (allN_spec hm k hk))

theorem itr_eq {P : Nat} {x : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P x) :
    ∀ (d : Nat) (p : Fin 1782), (((x ^ d) p : Fin 1782) : ℕ) = itr d P p
  | 0, p => rfl
  | d + 1, p => by
    rw [pow_succ', Equiv.Perm.mul_apply, ap h, itr_eq h d p]
    rfl

theorem pow_of {P : Nat} {x : Equiv.Perm (Fin 1782)} (h : PRep 1782 11 P x) {d : Nat}
    (hc : ∀ p < 1782, Nat.beq (itr d P p) p = true) : x ^ d = 1 :=
  ext1782 fun p => by
    rw [itr_eq h, Equiv.Perm.one_apply]
    exact Nat.eq_of_beq_eq_true (hc p p.2)

@[expose] noncomputable def ph (e₀ e₁ e₂ e₃ e₄ : ℕ) : Equiv.Perm (Fin 1782) :=
  aP 0 ^ e₀ * aP 1 ^ e₁ * aP 2 ^ e₂ * aP 3 ^ e₃ * aP 4 ^ e₄

theorem ev_eq (e₀ e₁ e₂ e₃ e₄ : ℕ) (p : Fin 1782) :
    ((ph e₀ e₁ e₂ e₃ e₄ p : Fin 1782) : ℕ) = ev e₀ e₁ e₂ e₃ e₄ p := by
  simp only [ph, Equiv.Perm.mul_apply]
  rw [itr_eq (pA (k := 0) (by norm_num)).1, itr_eq (pA (k := 1) (by norm_num)).1,
    itr_eq (pA (k := 2) (by norm_num)).1, itr_eq (pA (k := 3) (by norm_num)).1,
    itr_eq (pA (k := 4) (by norm_num)).1]
  rfl

theorem cube {j : Nat} (hj : j < 5) : aP j ^ 3 = 1 := by
  have h := cOK
  unfold cK at h
  exact pow_of (pA (by omega)).1 (allN_spec (allN_spec h j hj))

theorem comm {i j : Nat} (hi : i < 5) (hj : j < 5) : aP i * aP j = aP j * aP i := by
  have h := abOK
  unfold abK at h
  have h' := allN_spec (allN_spec h i hi) j hj
  refine ext1782 fun p => ?_
  simp only [Equiv.Perm.mul_apply, ap (pA (k := i) (by omega)).1, ap (pA (k := j) (by omega)).1]
  exact Nat.eq_of_beq_eq_true (allN_spec h' p p.2)

theorem g11 : aP 5 ^ 11 = 1 := by
  have h := gOK
  unfold gK at h
  exact pow_of (pA (by norm_num)).1 (allN_spec h)

theorem conj_gen {C CI P : Nat} {c e t : Equiv.Perm (Fin 1782)} (hc : PRep 1782 11 C c)
    (hci : PRep 1782 11 CI c⁻¹) (he : PRep 1782 11 P e) {F : Nat → Nat}
    (ht : ∀ p : Fin 1782, ((t p : Fin 1782) : ℕ) = F p)
    (h : ∀ p : Fin 1782, Nat.beq (fv C (fv P (fv CI p))) (F p) = true) : c * e * c⁻¹ = t :=
  ext1782 fun p => by
    simp only [Equiv.Perm.mul_apply, ap hc, ap hci, ap he, ht]
    exact Nat.eq_of_beq_eq_true (h p)

theorem nconj_gen {C CI P : Nat} {c e : Equiv.Perm (Fin 1782)} (hc : PRep 1782 11 C c)
    (hci : PRep 1782 11 CI c⁻¹) (he : PRep 1782 11 P e)
    (h : ∃ p < 1782, Nat.beq (fv C (fv P (fv CI p))) (fv P p) = false) : c * e * c⁻¹ ≠ e := by
  obtain ⟨p, hp, hn⟩ := h
  intro hce
  have e1 := congrArg (fun x : Equiv.Perm (Fin 1782) => ((x ⟨p, hp⟩ : Fin 1782) : ℕ)) hce
  simp only [Equiv.Perm.mul_apply, ap hc, ap hci, ap he] at e1
  rw [e1, Nat.beq_refl] at hn
  exact Bool.false_ne_true hn.symm

theorem conj_eq {j : Nat} (hj : j < 5) :
    aP 5 * aP j * (aP 5)⁻¹ = ph (ex j 0) (ex j 1) (ex j 2) (ex j 3) (ex j 4) := by
  have h := nOK
  unfold nK at h
  exact conj_gen (pA (k := 5) (by norm_num)).1 (pA (k := 5) (by norm_num)).2
    (pA (k := j) (by omega)).1 (F := evE j) (fun p => ev_eq _ _ _ _ _ p)
    (fun p => allN_spec (allN_spec h j hj) p p.2)

theorem ph_ne {e₀ e₁ e₂ e₃ e₄ : ℕ} (h₀ : e₀ < 3) (h₁ : e₁ < 3) (h₂ : e₂ < 3) (h₃ : e₃ < 3)
    (h₄ : e₄ < 3) (hne : e₀ + (e₁ + (e₂ + (e₃ + e₄))) ≠ 0) : ph e₀ e₁ e₂ e₃ e₄ ≠ 1 := by
  have h := wOK
  unfold wK at h
  have h' := allN_spec (allN_spec (allN_spec (allN_spec (allN_spec h e₀ h₀) e₁ h₁) e₂ h₂) e₃ h₃)
    e₄ h₄
  rcases bIf_tt h' with hz | hw
  · exact absurd (Nat.eq_of_beq_eq_true hz) hne
  · rw [strictB_val] at hw
    obtain ⟨hq, hm⟩ := (bAnd_iff _ _).1 hw
    have hq' : wt e₀ e₁ e₂ e₃ e₄ < 1782 := Nat.blt_eq.mp hq
    intro h1
    have e := ev_eq e₀ e₁ e₂ e₃ e₄ ⟨_, hq'⟩
    rw [h1, Equiv.Perm.one_apply] at e
    rw [← e, Nat.beq_refl] at hm
    exact Bool.false_ne_true (bIf_ff hm).symm

theorem nc : aP 5 * aP 0 * (aP 5)⁻¹ ≠ aP 0 := by
  have h := ncOK
  unfold ncK at h
  obtain ⟨p, hp, hn⟩ := anyN_spec h
  exact nconj_gen (pA (k := 5) (by norm_num)).1 (pA (k := 5) (by norm_num)).2
    (pA (k := 0) (by norm_num)).1 ⟨p, hp, bIf_ff hn⟩

@[expose] noncomputable def AS : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (Set.range fun j : Fin 5 => aP j)

theorem gen_mem (j : Fin 5) : aP j ∈ AS := Subgroup.subset_closure ⟨j, rfl⟩

theorem ph_mem (e₀ e₁ e₂ e₃ e₄ : ℕ) : ph e₀ e₁ e₂ e₃ e₄ ∈ AS := by
  unfold ph
  exact AS.mul_mem (AS.mul_mem (AS.mul_mem (AS.mul_mem (AS.pow_mem (gen_mem 0) _)
    (AS.pow_mem (gen_mem 1) _)) (AS.pow_mem (gen_mem 2) _)) (AS.pow_mem (gen_mem 3) _))
    (AS.pow_mem (gen_mem 4) _)

theorem AS_comm : ∀ a ∈ AS, ∀ b ∈ AS, a * b = b * a := by
  have hgc : ∀ x ∈ Set.range (fun j : Fin 5 => aP j), ∀ y ∈ Set.range (fun j : Fin 5 => aP j),
      x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact comm i.2 j.2
  have hstep1 : ∀ x ∈ Set.range (fun j : Fin 5 => aP j), AS ≤ Subgroup.centralizer {x} := by
    intro x hx
    rw [AS, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hgc y hy x hx
  intro a ha b hb
  have : AS ≤ Subgroup.centralizer {b} := by
    rw [AS, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hstep1 x hx hb)).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (this ha)

theorem AS_pow : ∀ a ∈ AS, a ^ 3 = 1 := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact cube j.2
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := AS_comm x hx y hy
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

@[reducible] noncomputable def ASComm : CommGroup AS :=
  { (inferInstance : Group AS) with
    mul_comm := fun x y => Subtype.ext (AS_comm x.1 x.2 y.1 y.2) }

theorem AS_card : Nat.card AS = 243 := by
  let _ : CommGroup AS := ASComm
  let y : Fin 5 → AS := fun j => ⟨aP j, gen_mem j⟩
  have hy3 : ∀ j, y j ^ 3 = 1 := fun j => Subtype.ext (by
    change aP j ^ 3 = 1
    exact cube j.2)
  let f : Multiplicative (Fin 5 → ZMod 3) → AS := fun e =>
    ∏ i, y i ^ (Multiplicative.toAdd e i).val
  have hf : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    simp only [f, toAdd_mul, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (hy3 i), pow_add]
  let ψ : Multiplicative (Fin 5 → ZMod 3) →* AS := MonoidHom.mk' f hf
  have hcoe : ∀ e, ((ψ e : AS) : Equiv.Perm (Fin 1782)) =
      ph (Multiplicative.toAdd e 0).val (Multiplicative.toAdd e 1).val
        (Multiplicative.toAdd e 2).val (Multiplicative.toAdd e 3).val
        (Multiplicative.toAdd e 4).val := by
    intro e
    change ((∏ i, y i ^ (Multiplicative.toAdd e i).val : AS) : Equiv.Perm (Fin 1782)) = _
    rw [Fin.prod_univ_five]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have hv : ∀ i, (Multiplicative.toAdd e i).val < 3 := fun i => ZMod.val_lt _
    refine ph_ne (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) ?_
      (by rw [← hcoe]; exact congrArg Subtype.val he)
    intro hz
    apply hne
    have h0 : (Multiplicative.toAdd e 0).val = 0 := by omega
    have h1 : (Multiplicative.toAdd e 1).val = 0 := by omega
    have h2 : (Multiplicative.toAdd e 2).val = 0 := by omega
    have h3 : (Multiplicative.toAdd e 3).val = 0 := by omega
    have h4 : (Multiplicative.toAdd e 4).val = 0 := by omega
    have hz' : ∀ i : Fin 5, (Multiplicative.toAdd e i).val = 0 := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have : Multiplicative.toAdd e = 0 := funext fun i => (ZMod.val_eq_zero _).1 (hz' i)
    rw [← ofAdd_toAdd e, this, ofAdd_zero]
  have hsurj : Function.Surjective ψ := by
    have key : ∀ x ∈ AS, ∃ e, ((ψ e : AS) : Equiv.Perm (Fin 1782)) = x := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        refine ⟨Multiplicative.ofAdd (Pi.single j 1), ?_⟩
        rw [hcoe]
        have : Fact (1 < 3) := ⟨by norm_num⟩
        fin_cases j <;> simp [ph, Pi.single_apply, ZMod.val_one]
      | one => exact ⟨1, congrArg Subtype.val (map_one ψ)⟩
      | mul x y _ _ ihx ihy =>
        obtain ⟨e, he⟩ := ihx
        obtain ⟨e', he'⟩ := ihy
        refine ⟨e * e', ?_⟩
        rw [← he, ← he']
        exact congrArg Subtype.val (map_mul ψ e e')
      | inv x _ ih =>
        obtain ⟨e, he⟩ := ih
        refine ⟨e⁻¹, ?_⟩
        rw [← he]
        exact congrArg Subtype.val (map_inv ψ e)
    intro c
    obtain ⟨e, he⟩ := key c.1 c.2
    exact ⟨e, Subtype.ext he⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)]
  change Nat.card (Fin 5 → ZMod 3) = 243
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem conj_mem : ∀ a ∈ AS, aP 5 * a * (aP 5)⁻¹ ∈ AS := by
  intro a ha
  have : AS ≤ AS.comap (MulAut.conj (aP 5)).toMonoidHom := by
    rw [AS, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change aP 5 * aP j * (aP 5)⁻¹ ∈ _
    rw [conj_eq j.2]
    exact ph_mem _ _ _ _ _
  have h' := this ha
  rw [Subgroup.mem_comap] at h'
  simpa [MulAut.conj_apply] using h'

theorem ag_facts :
    ∃ (A : Subgroup (Equiv.Perm (Fin 1782))) (g : Equiv.Perm (Fin 1782)), A ≤ suzM ∧
      g ∈ suzM ∧ Nat.card A = 243 ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      (∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧ g ^ 11 = 1 ∧ ∃ a ∈ A, g * a * g⁻¹ ≠ a := by
  refine ⟨AS, aP 5, ?_, mem_M (by norm_num), AS_card, AS_comm, AS_pow, conj_mem, g11,
    aP 0, gen_mem 0, nc⟩
  rw [AS, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact mem_M (by omega)

end CertificateChecks.KernelSpor.S129060

end
