
module

public import Certificates.Kernel.Misc.GL52.GL3

public section

namespace CertificateChecks.KernelMisc.GL52L

open CFSG.Literature.GL52 Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.KC.Misc.GLM

@[expose] def compKey (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

theorem keyPerm_getD {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (keyPerm σ).getD i.val 0 = (σ i : ℕ) := by
  rw [keyPerm, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

theorem keyPerm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    keyPerm (σ * τ) = compKey (keyPerm σ) (keyPerm τ) := by
  have h : ∀ i : Fin n, (keyPerm σ).getD (τ i : ℕ) 0 = ((σ * τ) i : ℕ) := fun i => by
    rw [keyPerm_getD, Equiv.Perm.mul_apply]
  simp only [compKey, keyPerm, List.map_map] at h ⊢
  exact List.map_congr_left fun i _ => (h i).symm

theorem keyPerm_inj {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : keyPerm σ = keyPerm τ) : σ = τ := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [← keyPerm_getD, ← keyPerm_getD, h]

theorem keyA5_mul (q r : alternatingGroup (Fin 5)) :
    keyA5 (q * r) = compKey (keyA5 q) (keyA5 r) :=
  keyPerm_mul (q : Equiv.Perm (Fin 5)) r

theorem keyA5_inj {q r : alternatingGroup (Fin 5)} (h : keyA5 q = keyA5 r) : q = r :=
  Subtype.ext (keyPerm_inj h)

abbrev ent (a : List ℕ) (i k : Fin 3) : ℕ := a.getD (3 * i.val + k.val) 0

@[expose] def mulKey (a b : List ℕ) : List ℕ :=
  (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j =>
    (ent a i 0 * ent b 0 j + ent a i 1 * ent b 1 j + ent a i 2 * ent b 2 j) % 2

@[expose] def mulVecKey (a v : List ℕ) : List ℕ :=
  (List.finRange 3).map fun i =>
    (ent a i 0 * v.getD 0 0 + ent a i 1 * v.getD 1 0 + ent a i 2 * v.getD 2 0) % 2

theorem val_three (a₀ a₁ a₂ b₀ b₁ b₂ : ZMod 2) :
    (a₀ * b₀ + a₁ * b₁ + a₂ * b₂).val =
      (a₀.val * b₀.val + a₁.val * b₁.val + a₂.val * b₂.val) % 2 := by
  revert a₀ a₁ a₂ b₀ b₁ b₂
  decide

theorem keyGL3_ent (M : GL (Fin 3) (ZMod 2)) (i k : Fin 3) :
    ent (keyGL3 M) i k = ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) i k).val := by
  fin_cases i <;> fin_cases k <;> rfl

theorem keyVec_getD (c : Multiplicative (Fin 3 → ZMod 2)) (j : Fin 3) :
    (keyVec c).getD j.val 0 = (c.toAdd j).val := by
  fin_cases j <;> rfl

theorem keyGL3_mul (q r : GL (Fin 3) (ZMod 2)) :
    keyGL3 (q * r) = mulKey (keyGL3 q) (keyGL3 r) := by
  simp only [mulKey, keyGL3_ent]
  unfold keyGL3
  refine List.flatMap_congr fun i _ => List.map_congr_left fun j _ => ?_
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, val_three]

theorem keyVec_glAct (M : GL (Fin 3) (ZMod 2)) (c : Multiplicative (Fin 3 → ZMod 2)) :
    keyVec (glAct M c) = mulVecKey (keyGL3 M) (keyVec c) := by
  simp only [mulVecKey, keyGL3_ent]
  have h₀ := keyVec_getD c 0
  have h₁ := keyVec_getD c 1
  have h₂ := keyVec_getD c 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h₀ h₁ h₂
  rw [h₀, h₁, h₂]
  unfold keyVec
  refine List.map_congr_left fun i _ => ?_
  change (((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c.toAdd) i).val = _
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three, val_three]

theorem keyGL3_inj {M N : GL (Fin 3) (ZMod 2)} (h : keyGL3 M = keyGL3 N) : M = N :=
  List.inj_on_of_nodup_map gl3Elems_ok.1 (mem_gl3Elems_of gl3Elems_ok M)
    (mem_gl3Elems_of gl3Elems_ok N) h

theorem vec_one : ∀ c : Multiplicative (Fin 3 → ZMod 2), lkWord keyVec tblE8 c = [] → c = 1 := by
  decide +kernel

theorem keyVec_mem' : ∀ c : Multiplicative (Fin 3 → ZMod 2), hasKey tblE8 (keyVec c) = true := by
  decide +kernel

theorem keyA5_mem' : ∀ σ : alternatingGroup (Fin 5), hasKey tblA5 (keyA5 σ) = true := by
  decide +kernel

theorem mem_of_isSome {Q : Type*} {L : List (List ℕ × List ℤ)} {key : Q → List ℕ}
    (h : ∀ q, hasKey L (key q) = true) (q : Q) : ∃ e ∈ L, e.1 = key q :=
  mem_of_hasKey (h q)

noncomputable abbrev lkK (gs : List G) (L : List (List ℕ × List ℤ)) (k : List ℕ) : ℕ :=
  wK gs (lkW L k)

theorem tblEq_wT_id (gs : List G) (w : List ℤ) :
    tblEq 31 (wT gs w) (idT 31) = (wK gs w == idK) := by
  rw [tblEq_rep (rep_wT gs w) (Rep.idT (by norm_num)), cG_one, cG_wordG]

theorem tblEq_comp_id (gs₁ gs₂ : List G) (w₁ w₂ : List ℤ) :
    tblEq 31 (compT 31 (wT gs₁ w₁) (wT gs₂ w₂)) (idT 31) =
      (mmulK (wK gs₁ w₁) (wK gs₂ w₂) == idK) := by
  rw [tblEq_rep (Rep.compT (rep_wT gs₁ w₁) (rep_wT gs₂ w₂)) (Rep.idT (by norm_num)), cG_mul,
    cG_one, cG_wordG, cG_wordG]

theorem tblEq_wT_comp3 (gs gs₁ gs₂ : List G) (w w₁ w₂ w₃ : List ℤ) :
    tblEq 31 (wT gs w) (compT 31 (compT 31 (wT gs₁ w₁) (wT gs₂ w₂)) (wT gs₁ w₃)) =
      (wK gs w == mmulK (mmulK (wK gs₁ w₁) (wK gs₂ w₂)) (wK gs₁ w₃)) := by
  rw [tblEq_rep (rep_wT gs w) (Rep.compT (Rep.compT (rep_wT gs₁ w₁) (rep_wT gs₂ w₂))
    (rep_wT gs₁ w₃)), cG_mul, cG_mul, cG_wordG, cG_wordG, cG_wordG, cG_wordG]

theorem mulOK_of {Q : Type*} [Mul Q] (gs : List G) (key : Q → List ℕ)
    (L : List (List ℕ × List ℤ)) (comb : List ℕ → List ℕ → List ℕ)
    (hkey : ∀ q r, key (q * r) = comb (key q) (key r)) (hcov : ∀ q, ∃ e ∈ L, e.1 = key q)
    (hchk : (L.all fun e => L.all fun e' =>
      lkK gs L (comb e.1 e'.1) == mmulK (lkK gs L e.1) (lkK gs L e'.1)) = true) (q r : Q) :
    tblEq 31 (lkTableT (genTables gs) (genInvTables gs) key L (q * r))
      (compT 31 (lkTableT (genTables gs) (genInvTables gs) key L q)
        (lkTableT (genTables gs) (genInvTables gs) key L r)) = true := by
  obtain ⟨e, he, hq⟩ := hcov q
  obtain ⟨e', he', hr⟩ := hcov r
  have h : (L.all fun e' =>
      lkK gs L (comb e.1 e'.1) == mmulK (lkK gs L e.1) (lkK gs L e'.1)) = true :=
    List.all_eq_true.1 hchk e he
  have h' : (lkK gs L (comb e.1 e'.1) == mmulK (lkK gs L e.1) (lkK gs L e'.1)) = true :=
    List.all_eq_true.1 h e' he'
  change tblEq 31 (wT gs (lkW L (key (q * r))))
    (compT 31 (wT gs (lkW L (key q))) (wT gs (lkW L (key r)))) = true
  rw [tblEq_wT_comp, hkey, ← hq, ← hr]
  exact h'

theorem injOK_of {Q : Type*} [One Q] (gs : List G) (key : Q → List ℕ)
    (L : List (List ℕ × List ℤ)) (k₁ : List ℕ) (hinj : ∀ q, key q = k₁ → q = 1)
    (hcov : ∀ q, ∃ e ∈ L, e.1 = key q)
    (hchk : (L.all fun e => !(lkK gs L e.1 == idK) || e.1 == k₁) = true) (q : Q)
    (hq : tblEq 31 (lkTableT (genTables gs) (genInvTables gs) key L q) (idT 31) = true) :
    q = 1 := by
  obtain ⟨e, he, hk⟩ := hcov q
  have h : (!(lkK gs L e.1 == idK) || e.1 == k₁) = true := List.all_eq_true.1 hchk e he
  change tblEq 31 (wT gs (lkW L (key q))) (idT 31) = true at hq
  rw [tblEq_wT_id, ← hk] at hq
  change (lkK gs L e.1 == idK) = true at hq
  rw [hq] at h
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact hinj q (hk ▸ h)

theorem all_of_chunks {α : Type*} (p : α → Bool) (s : ℕ) :
    ∀ (m : ℕ) (l : List α), l.length ≤ s * m →
      (∀ i < m, ((l.drop (s * i)).take s).all p = true) → l.all p = true
  | 0, l, hl, _ => by
    have hl₀ : l = [] := List.eq_nil_of_length_eq_zero (by rw [Nat.mul_zero] at hl; omega)
    subst hl₀
    rfl
  | m + 1, l, hl, h => by
    rw [← List.take_append_drop s l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks p s m (l.drop s) ?_ fun i hi => ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      omega
    · have e : (l.drop s).drop (s * i) = l.drop (s * (i + 1)) := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [e]
      exact h (i + 1) (by omega)

end CertificateChecks.KernelMisc.GL52L

end
