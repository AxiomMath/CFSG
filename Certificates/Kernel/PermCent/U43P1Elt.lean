module

public import Certificates.Kernel.PermCent.U43P1Mat
public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UAut
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UBridgeBase

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb Matrix Subgroup
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def glK (k : ℕ) : GL (Fin 4) F9 :=
  if h : IsUnit (matK k).det then GeneralLinearGroup.mk'' (matK k) h else 1

theorem glK_val {k : ℕ} (h : (matK k).det ≠ 0) :
    (glK k : Matrix (Fin 4) (Fin 4) F9) = matK k := by
  rw [glK, dif_pos (isUnit_iff_ne_zero.mpr h)]
  rfl

@[expose] noncomputable def eK (k : ℕ) (ε : Bool) : Equiv.Perm (Fin 820) :=
  perm820 (glK k) * frob820 ^ ε.toNat

theorem eK_apply {k : ℕ} {ε : Bool} (h : (matK k).det ≠ 0) (i : Fin 820) :
    (eK k ε i : ℕ) = imgK k ε i := by
  cases ε
  · simp only [eK, Bool.toNat_false, pow_zero, mul_one]
    rw [perm820_apply, glK_val h, mulVec_eq_mv4]
    rfl
  · simp only [eK, Bool.toNat_true, pow_one, Equiv.Perm.mul_apply]
    rw [perm820_apply, frob820_apply]
    obtain ⟨c, hc, h'⟩ := decode_ptIndex (barV_ne_zero (decode_ne_zero i))
    rw [h', Matrix.mulVec_smul, ptIndex_smul hc, glK_val h, mulVec_eq_mv4]
    rfl

theorem imgK_lt (k : ℕ) (ε : Bool) (i : ℕ) : imgK k ε i < 2 ^ 10 :=
  (ptIndex_lt _).trans (by norm_num)

theorem prep_pk {k : ℕ} {ε : Bool} (h : (matK k).det ≠ 0) : PRep 820 10 (pk k ε) (eK k ε) := by
  intro x
  rw [eK_apply h, pk, CFSG.Certificates.Kernel.PkCV.pg_pmk (by norm_num)
    (fun y _ => imgK_lt k ε y) x.2]

theorem prep_matOK {k p : ℕ} {ε : Bool} (h : (matK k).det ≠ 0) (hm : matOK k ε p = true) :
    PRep 820 10 p (eK k ε) := by
  intro x
  rw [matOK, List.all_eq_true] at hm
  rw [eK_apply h]
  exact Nat.eq_of_beq_eq_true (hm x (List.mem_range.2 x.2))

@[expose] def detOf (k : ℕ) : ℕ := ((matDets.find? fun x => x.1 == k).map Prod.snd).getD 0

theorem uncode_matDets : ∀ x ∈ matDets, uncode x.2 ≠ 0 := by decide

theorem isUnitaryF_glK {k : ℕ} (h : (matK k).det ≠ 0)
    (hu : ((matK k).map (· ^ 3))ᵀ * matK k = 1) : IsUnitaryF (glK k) := by
  have hpow : (matK k).map (· ^ 3) = (matK k).map barF :=
    Matrix.ext fun i j => (barF_eq_pow _).symm
  unfold IsUnitaryF
  rw [glK_val h, ← hpow]
  exact hu

theorem detOf_spec {k : ℕ} (h : detOf k ≠ 0) :
    (matK k).det ≠ 0 ∧ IsUnitaryF (glK k) ∧
      (glK k : Matrix (Fin 4) (Fin 4) F9).det = uncode (detOf k) := by
  unfold detOf at h ⊢
  cases hf : matDets.find? (fun x => x.1 == k) with
  | none => rw [hf] at h; exact absurd rfl h
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hk : x.1 = k := by simpa using List.find?_some hf
    obtain ⟨hu, hd⟩ := matDets_ok x hx
    rw [hk] at hu hd
    have h0 : (matK k).det ≠ 0 := by rw [hd]; exact uncode_matDets x hx
    refine ⟨h0, isUnitaryF_glK h0 hu, ?_⟩
    rw [glK_val h0, hd]
    rfl

theorem uncode_three : uncode 3 = 1 := by decide

theorem eK_mem_range {k : ℕ} (h : detOf k = 3) : eK k false ∈ psi.range := by
  obtain ⟨-, hu, hd⟩ := detOf_spec (by rw [h]; norm_num)
  have e : eK k false = perm820 (glK k) := by simp [eK]
  rw [e]
  exact perm820_mem_range hu (by rw [hd, h, uncode_three])

theorem isUnitaryF_mul {A B : GL (Fin 4) F9} (hA : IsUnitaryF A) (hB : IsUnitaryF B) :
    IsUnitaryF (A * B) := by
  have hmul : ∀ M N : Matrix (Fin 4) (Fin 4) F9, (M * N).map barF = M.map barF * N.map barF :=
    fun M N => Matrix.map_mul (f := (barEquiv : F9 →+* F9))
  have hA' : ((A : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ * (A : Matrix (Fin 4) (Fin 4) F9) = 1 :=
    hA
  have hB' : ((B : Matrix (Fin 4) (Fin 4) F9).map barF)ᵀ * (B : Matrix (Fin 4) (Fin 4) F9) = 1 :=
    hB
  unfold IsUnitaryF
  rw [Units.val_mul, hmul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (A : Matrix (Fin 4) (Fin 4) F9), hA', Matrix.one_mul, hB']

theorem det_conj (A B : GL (Fin 4) F9) :
    ((A * B * A⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).det =
      (B : Matrix (Fin 4) (Fin 4) F9).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem unitary_of_mem {g : GL (Fin 4) F9} (hg : g ∈ unitarySU 3 1 F9 4) :
    IsUnitaryF g ∧ (g : Matrix (Fin 4) (Fin 4) F9).det = 1 := by
  obtain ⟨hd, hu⟩ := (mem_unitarySU_iff unitaryFieldData).mp hg
  have hm : (g : Matrix (Fin 4) (Fin 4) F9).map unitaryFieldData.bar =
      (g : Matrix (Fin 4) (Fin 4) F9).map barF := Matrix.ext fun i j => bar_eq_barF _
  refine ⟨?_, hd⟩
  unfold IsUnitaryF
  rw [← hm]
  exact hu

theorem perm820_frob_mem_normalizer {A : GL (Fin 4) F9} (hA : IsUnitaryF A) {ε : ℕ}
    (hε : ε ≤ 1) :
    perm820 A * frob820 ^ ε ∈ normalizer (psi.range : Set (Equiv.Perm (Fin 820))) := by
  set σ := perm820 A * frob820 ^ ε
  have key : ∀ x ∈ psi.range, σ * x * σ⁻¹ ∈ psi.range := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := theta_surjective q
    obtain ⟨g', hg', he⟩ : ∃ g' : GL (Fin 4) F9, g' ∈ unitarySU 3 1 F9 4 ∧
        frob820 ^ ε * perm820 (g : GL (Fin 4) F9) * (frob820 ^ ε)⁻¹ = perm820 g' := by
      interval_cases ε
      · exact ⟨g, g.2, by rw [pow_zero, one_mul, inv_one, mul_one]⟩
      · refine ⟨glAut barEquiv g, CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.glAut_mem_unitarySU unitaryFieldData barEquiv g.2, ?_⟩
        rw [pow_one]
        exact frob820_conj _ _ (by rw [coe_glAut]; rfl)
    obtain ⟨hu, hd⟩ := unitary_of_mem hg'
    have hσ : σ = perm820 A * frob820 ^ ε := rfl
    have e : σ * psi (theta g) * σ⁻¹ = perm820 (A * g' * A⁻¹) := by
      rw [psi_theta, map_mul, map_mul, map_inv, ← he, hσ]
      group
    rw [e]
    exact perm820_mem_range (isUnitaryF_mul_inv (isUnitaryF_mul hA hu) hA) (by rw [det_conj, hd])
  have hmap : psi.range.map (MulAut.conj σ).toMonoidHom ≤ psi.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact key x hx
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hmap
    (by rw [card_map_of_injective (MulAut.conj σ).injective]))

@[expose] noncomputable def genX (k : ℕ) : X₀ := if k = 0 then xElt else yElt

theorem genX_image : (fun k => psi (genX k)) '' {k | k < 2} = {psi xElt, psi yElt} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (by rw [genX, if_pos rfl])
    · exact Or.inr (by rw [genX, if_neg (by norm_num)])
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by rw [genX, if_pos rfl]⟩
    · exact ⟨1, by norm_num, by rw [genX, if_neg (by norm_num)]⟩

theorem closure_gen :
    closure ((fun k => psi (genX k)) '' {k | k < 2}) = psi.range := by
  rw [genX_image, range_psi]

theorem prep_tabOK {a : Array ℕ} {p : ℕ} {g : Equiv.Perm (Fin 820)}
    (hr : CFSG.Monster.B.Co2.Rep 820 a g) (h : tabOK a p = true) : PRep 820 10 p g := by
  intro x
  rw [tabOK, List.all_eq_true] at h
  rw [← hr x]
  exact Nat.eq_of_beq_eq_true (h x (List.mem_range.2 x.2))

theorem prep_psi_gen {G : ℕ → ℕ} (h0 : tabOK tabA (G 0) = true) (h1 : tabOK tabB (G 1) = true) :
    ∀ k < 2, PRep 820 10 (G k) (psi (genX k)) := by
  intro k hk
  interval_cases k
  · rw [genX, if_pos rfl]
    exact prep_tabOK rep_tabA h0
  · rw [genX, if_neg (by norm_num)]
    exact prep_tabOK rep_tabB h1

end CertificateChecks.KernelPermCent.U43P1

end
