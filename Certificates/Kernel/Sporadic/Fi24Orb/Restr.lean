
module

public import Certificates.Kernel.Sporadic.Fi24Orb.Psi
public import CFSG.Certificates.Kernel.Spor.Fi24OrbTheory
public import CFSG.Sporadic.Fi23.Setup
import Certificates.Kernel.Sporadic.Fi24Fix.Init
import Certificates.Kernel.Sporadic.Fi24Fix.Chain
import Certificates.Kernel.Sporadic.Fi24Orb.M
import Certificates.Kernel.Sporadic.Fi24Orb.Small
import Certificates.Kernel.Fi23M.Facts
public import CFSG.Sporadic.Fi23.Simple
public import Certificates.Data.CFSGNative.Fi23.Certificate

public section

namespace CertificateChecks.KernelFi24Orb

open CertificateChecks.KernelFi24Fix CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK
  CFSG.KC.Fi24Orb CFSG.KC.Fi24OrbS CFSG.KC.Fi24OrbT CFSG.KD.Fi24Orb CFSG.KS.Mat3

noncomputable abbrev Rm : Matrix (Fin 781) (Fin 781) (ZMod 3) := mat3 781 609961 CFSG.KD.Fi24Fix.R

noncomputable abbrev Mb : Matrix (Fin 781) (Fin 253) (ZMod 3) :=
  fun i j => Rm i (Fin.castLE (by norm_num) j)

theorem R_entries : (∀ i j : Fin 781, 253 ≤ j.val → Rm i j = 0) ∧
    ∀ i j : Fin 781, i.val < 253 → Rm i j = if i.val = j.val then 1 else 0 := by
  have hr := rowsZOK_spec CFSG.KD.Fi24Fix.init_rows
  have hb1 : ∀ p < 609961, CFSG.KD.Fi24Fix.R1.testBit p = CFSG.KD.Fi24Fix.R.testBit p := by
    intro p hp
    change (CFSG.KD.Fi24Fix.R &&& CFSG.KD.BrFi24.LO).testBit p = _
    rw [Nat.testBit_and, show CFSG.KD.BrFi24.LO = 2 ^ 609961 - 1 from pow_sub_one_eq 609961,
      Nat.testBit_two_pow_sub_one]
    simp [hp]
  have hb2 : ∀ p, CFSG.KD.Fi24Fix.R2.testBit p = CFSG.KD.Fi24Fix.R.testBit (609961 + p) := by
    intro p
    change (CFSG.KD.Fi24Fix.R >>> 609961).testBit p = _
    rw [Nat.testBit_shiftRight]
  have hent : ∀ i j : Fin 781, Rm i j = bv (CFSG.KD.Fi24Fix.R1.testBit (781 * i.val + j.val))
      (CFSG.KD.Fi24Fix.R2.testBit (781 * i.val + j.val)) := by
    intro i j
    rw [hb1 _ (by omega), hb2]
    rfl
  refine ⟨fun i j hj => ?_, fun i j hi => ?_⟩
  · rw [hent]
    by_cases hi : i.val < 253
    · obtain ⟨a, b⟩ := (hr i i.isLt j j.isLt).1 hi
      have e : j.val ≠ i.val := by omega
      rw [a, b]
      simp [e, bv]
    · obtain ⟨a, b⟩ := (hr i i.isLt j j.isLt).2 (by omega) hj
      rw [a, b]
      rfl
  · rw [hent]
    obtain ⟨a, b⟩ := (hr i i.isLt j j.isLt).1 hi
    rw [a, b]
    by_cases e : j.val = i.val
    · simp [e, bv]
    · simp [e, Ne.symm e, bv]

theorem top_Mb : top (by norm_num : 253 ≤ 781) Mb = 1 := by
  ext i j
  change Rm (Fin.castLE _ i) (Fin.castLE _ j) = _
  rw [R_entries.2 _ _ (by simp), Matrix.one_apply]
  simp [Fin.ext_iff]

noncomputable abbrev Pp : Matrix (Fin 253) (Fin 781) (ZMod 3) :=
  fun j i => if i.val = j.val then 1 else 0

noncomputable abbrev Ei : Matrix (Fin 781) (Fin 253) (ZMod 3) :=
  fun i j => if i.val = j.val then 1 else 0

theorem Pp_Ei : Pp * Ei = 1 := by
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (Fin.castLE (by norm_num) j)]
  · simp only [Pp, Ei, Fin.coe_castLE, if_true, one_mul]
    by_cases h : j = l
    · subst h
      simp
    · have : (j : ℕ) ≠ l := fun e => h (Fin.ext e)
      simp [h, this]
  · intro i _ hi
    have : (i : ℕ) ≠ j := fun e => hi (Fin.ext (by simp [e]))
    simp [Pp, this]
  · simp

theorem Rm_eq : Rm = Mb * Pp := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : j.val < 253
  · rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · simp only [Pp, if_true, mul_one]
      rfl
    · intro l _ hl
      have : j.val ≠ l.val := fun h => hl (Fin.ext h.symm)
      simp [this]
    · simp
  · rw [R_entries.1 i j (by omega), Finset.sum_eq_zero]
    intro l _
    have : j.val ≠ l.val := by omega
    simp [this]

theorem Rm_Ei : Rm * Ei = Mb := by
  rw [Rm_eq, Matrix.mul_assoc, Pp_Ei, Matrix.mul_one]

theorem colSp_Mb : colSp Mb = (CFSG.Sporadic.Fi24.pt 0).sp := by
  rw [← root_eq]
  change colSp Mb = LinearMap.range Rm.mulVecLin
  rw [Rm_eq, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have : LinearMap.range Pp.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨Ei.mulVec v, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Pp_Ei, Matrix.one_mulVec]
  rw [this, Submodule.map_top]

@[expose] noncomputable def wU : List ℕ → GL (Fin 781) (ZMod 3)
  | [] => 1
  | k :: w => (if k = 23 then uA else uB) * wU w

theorem canon_RB {r : ℕ} (h0 : 0 < r) (h : r < 25) : Canon3 609961 (CFSG.KD.BrFi24.RB r) :=
  (CertificateChecks.KernelSpor.Fi24Rels.hregs r h0 h).1

theorem mat_RB23 : mat3 781 609961 (CFSG.KD.BrFi24.RB 23) = (uA : Matrix (Fin 781) (Fin 781) (ZMod 3)) := by
  rw [uA_val, CFSG.Sporadic.Fi24.mA, CertificateChecks.KernelSpor.Fi24Rels.mA_eq]

theorem mat_RB24 : mat3 781 609961 (CFSG.KD.BrFi24.RB 24) = (uB : Matrix (Fin 781) (Fin 781) (ZMod 3)) := by
  rw [uB_val, CFSG.Sporadic.Fi24.mB, CertificateChecks.KernelSpor.Fi24Rels.mB_eq]

theorem wordMul_wU : ∀ (w : List ℕ), (∀ k ∈ w, k = 23 ∨ k = 24) → ∀ {Y : ℕ}, Canon3 609961 Y →
    Canon3 609961 (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w Y) ∧
      mat3 781 609961 (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w Y) =
        (wU w : Matrix (Fin 781) (Fin 781) (ZMod 3)) * mat3 781 609961 Y
  | [], _, Y, hY => ⟨hY, by simp [CFSG.KC.Fi24Fix.wordMul, wU]⟩
  | k :: w, hw, Y, hY => by
    obtain ⟨h1, h2⟩ := wordMul_wU w (fun k' hk' => hw k' (List.mem_cons_of_mem k hk')) hY
    have hk := hw k List.mem_cons_self
    have hc : Canon3 609961 (CFSG.KD.BrFi24.RB k) := by
      rcases hk with rfl | rfl
      · exact canon_RB (by norm_num) (by norm_num)
      · exact canon_RB (by norm_num) (by norm_num)
    have e : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB (k :: w) Y =
        CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB k)
          (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w Y) := rfl
    obtain ⟨h3, h4⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ hc h1
    rw [e]
    refine ⟨h3, ?_⟩
    rw [h4, h2, wU, Units.val_mul, Matrix.mul_assoc]
    congr 1
    rcases hk with rfl | rfl
    · rw [if_pos rfl, mat_RB23]
    · rw [if_neg (by norm_num), mat_RB24]

theorem wordMul_cons (k : ℕ) (w : List ℕ) (Y : ℕ) :
    CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB (k :: w) Y =
      CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB k)
        (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w Y) := rfl

theorem wordMul_append (u v : List ℕ) (Y : ℕ) :
    CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB (u ++ v) Y =
      CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB u
        (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB v Y) := by
  induction u with
  | nil => rfl
  | cons k u ih => rw [List.cons_append, wordMul_cons, wordMul_cons, ih]

theorem W1_split : W1 = segW W1 0 2 ++ segW W1 2 8 ++ segW W1 10 8 ++ segW W1 18 8 ++
    segW W1 26 8 := by decide +kernel

theorem W2_split : W2 = segW W2 0 2 ++ segW W2 2 8 ++ segW W2 10 8 ++ segW W2 18 8 ++
    segW W2 26 8 ++ segW W2 34 8 := by decide +kernel

theorem W1_lt : ∀ k ∈ W1, k = 23 ∨ k = 24 := by decide +kernel

theorem W2_lt : ∀ k ∈ W2, k = 23 ∨ k = 24 := by decide +kernel

theorem W1R : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB W1 R = MX 4 := by
  rw [W1_split]
  simp only [List.append_assoc, wordMul_append]
  rw [Nat.eq_of_beq_eq_true seg1_26, Nat.eq_of_beq_eq_true seg1_18, Nat.eq_of_beq_eq_true seg1_10,
    Nat.eq_of_beq_eq_true seg1_2, Nat.eq_of_beq_eq_true seg1_0]

theorem W2R : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB W2 R = MX 10 := by
  rw [W2_split]
  simp only [List.append_assoc, wordMul_append]
  rw [Nat.eq_of_beq_eq_true seg2_34, Nat.eq_of_beq_eq_true seg2_26, Nat.eq_of_beq_eq_true seg2_18,
    Nat.eq_of_beq_eq_true seg2_10, Nat.eq_of_beq_eq_true seg2_2, Nat.eq_of_beq_eq_true seg2_0]

theorem canon_R : Canon3 609961 R := canon_of_vld (andB_true3 CFSG.KD.Fi24Fix.valid).1

noncomputable abbrev W1u : GL (Fin 781) (ZMod 3) := wU W1

noncomputable abbrev W2u : GL (Fin 781) (ZMod 3) := wU W2

theorem W_mat {w : List ℕ} {X : ℕ} (hw : ∀ k ∈ w, k = 23 ∨ k = 24)
    (hX : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w R = X) :
    Canon3 609961 X ∧ (wU w : Matrix (Fin 781) (Fin 781) (ZMod 3)) * Rm = mat3 781 609961 X := by
  obtain ⟨h1, h2⟩ := wordMul_wU w hw canon_R
  rw [hX] at h1 h2
  exact ⟨h1, h2.symm⟩

theorem stab_of {g : GL (Fin 781) (ZMod 3)} {Y : Matrix (Fin 781) (Fin 781) (ZMod 3)}
    (h1 : (g : Matrix (Fin 781) (Fin 781) (ZMod 3)) * Rm = Y) (h2 : Rm * Y = Y) :
    g ∈ stab (LinearMap.range Rm.mulVecLin) := by
  have hle : act g (LinearMap.range Rm.mulVecLin) ≤ LinearMap.range Rm.mulVecLin := by
    unfold act
    rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, h1, ← h2, Matrix.mulVecLin_mul,
      LinearMap.range_comp]
    exact LinearMap.map_le_range
  rw [mem_stab]
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) := by
    intro v w hvw
    have := congrArg (Matrix.mulVecLin ((g⁻¹ : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3))) hvw
    simpa [Matrix.mulVec_mulVec] using this
  have hcoe : ((act g (LinearMap.range Rm.mulVecLin) : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
      Set (Fin 781 → ZMod 3)) = (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) ''
        (LinearMap.range Rm.mulVecLin) := Submodule.map_coe _ _
  have hsub : ((act g (LinearMap.range Rm.mulVecLin) : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
      Set (Fin 781 → ZMod 3)) ⊆ LinearMap.range Rm.mulVecLin := hle
  have e := Set.eq_of_subset_of_ncard_le hsub (by rw [hcoe, Set.ncard_image_of_injective _ hinj])
    (Set.toFinite _)
  exact SetLike.coe_injective e

theorem colSp_eq : colSp Mb = LinearMap.range Rm.mulVecLin := by
  rw [colSp_Mb, ← root_eq]

theorem W_stab {w : List ℕ} {X : ℕ} (hw : ∀ k ∈ w, k = 23 ∨ k = 24)
    (hX : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w R = X)
    (hfix : CFSG.KD.BrFi24.MUL R X = X) : wU w ∈ stab (colSp Mb) := by
  obtain ⟨hc, h1⟩ := W_mat hw hX
  obtain ⟨-, e⟩ := CertificateChecks.KernelSpor.Fi24Rels.hs.mul_sound _ _ canon_R hc
  rw [hfix] at e
  rw [colSp_eq]
  exact stab_of h1 e.symm

theorem fix1 : CFSG.KD.BrFi24.MUL R (MX 4) = MX 4 := by
  have h := Nat.eq_of_beq_eq_true fixR1
  exact h

theorem fix2 : CFSG.KD.BrFi24.MUL R (MX 10) = MX 10 := by
  have h := Nat.eq_of_beq_eq_true fixR2
  exact h

theorem W1_stab : W1u ∈ stab (colSp Mb) := W_stab W1_lt W1R fix1

theorem W2_stab : W2u ∈ stab (colSp Mb) := W_stab W2_lt W2R fix2

noncomputable abbrev ρ : stab (colSp Mb) →* GL (Fin 253) (ZMod 3) := restrHom top_Mb

theorem top_Ei (X : Matrix (Fin 781) (Fin 781) (ZMod 3)) (i j : Fin 253) :
    top (by norm_num : 253 ≤ 781) (X * Ei) i j = X (Fin.castLE (by norm_num) i) (Fin.castLE (by norm_num) j) := by
  change (X * Ei) (Fin.castLE _ i) j = _
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE (by norm_num) j)]
  · simp [Ei]
  · intro b _ hb
    have : (b : ℕ) ≠ j := fun e => hb (Fin.ext (by simp [e]))
    simp [Ei, this]
  · simp

theorem ρ_val {w : List ℕ} {X C : ℕ} (hw : ∀ k ∈ w, k = 23 ∨ k = 24)
    (hX : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.RB w R = X)
    (hag : agreeOK X C = true) (hs : wU w ∈ stab (colSp Mb)) :
    ((ρ ⟨wU w, hs⟩ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) =
      mat3 253 64009 C := by
  rw [restrHom_val]
  change top _ ((wU w : Matrix (Fin 781) (Fin 781) (ZMod 3)) * Mb) = _
  rw [← Rm_Ei, ← Matrix.mul_assoc, (W_mat hw hX).2]
  ext i j
  rw [top_Ei]
  obtain ⟨a, b⟩ := agreeOK_spec hag i.val i.isLt j.val j.isLt
  unfold mat3
  simp only [Fin.coe_castLE]
  rw [a, b]

theorem ρ_W1 : ((ρ ⟨W1u, W1_stab⟩ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) =
    mat3 253 64009 (RS 0) := ρ_val W1_lt W1R agree1 W1_stab

theorem ρ_W2 : ((ρ ⟨W2u, W2_stab⟩ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) =
    mat3 253 64009 (RS 1) := ρ_val W2_lt W2R agree2 W2_stab

noncomputable abbrev Sρ : Subgroup (GL (Fin 253) (ZMod 3)) :=
  Subgroup.closure {ρ ⟨W1u, W1_stab⟩, ρ ⟨W2u, W2_stab⟩}

theorem slp_mem : ∀ k < 120, ∃ u ∈ Sρ,
    (u : Matrix (Fin 253) (Fin 253) (ZMod 3)) = mat3 253 64009 (RS k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨-, hst⟩ := slp_all k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · interval_cases k
      · exact ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), ρ_W1⟩
      · exact ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), ρ_W2⟩
    · obtain ⟨i, hi, j, hj, e⟩ := hst h2
      obtain ⟨u, hu, eu⟩ := ih i hi (by omega)
      obtain ⟨v, hv, ev⟩ := ih j hj (by omega)
      have ci : Canon3 64009 (RS i) := CertificateChecks.KernelFi23M.hs.vld_q _ (slp_all i (by omega)).1
      have cj : Canon3 64009 (RS j) := CertificateChecks.KernelFi23M.hs.vld_q _ (slp_all j (by omega)).1
      obtain ⟨-, em⟩ := CertificateChecks.KernelFi23M.hs.mul_sound _ _ ci cj
      refine ⟨u * v, Sρ.mul_mem hu hv, ?_⟩
      change mat3 253 64009 (CFSG.KD.Fi23M.MUL (RS i) (RS j)) = _ at em
      rw [Units.val_mul, eu, ev, ← em]
      change mat3 253 64009 (MUL3 (RS i) (RS j)) = _
      rw [e]

theorem andB_true' {a b : Bool} (h : CFSG.KC.Fi24Orb.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Fi24Orb.andB]

theorem pc_facts : CFSG.KD.Fi23M.VLD (RS 120) = true ∧ CFSG.KD.Fi23M.VLD (RS 121) = true ∧
    CFSG.KD.Fi23M.MUL (RS 120) (RS 121) = CFSG.KD.Fi23M.ONE := by
  obtain ⟨h1, h2⟩ := andB_true' pc_inv
  obtain ⟨h2, h3⟩ := andB_true' h2
  have h4 := Nat.eq_of_beq_eq_true h3
  exact ⟨h1, h2, h4⟩

theorem pc_mul : mat3 253 64009 (RS 120) * mat3 253 64009 (RS 121) = 1 := by
  obtain ⟨h1, h2, h3⟩ := pc_facts
  obtain ⟨-, e⟩ := CertificateChecks.KernelFi23M.hs.mul_sound _ _
    (CertificateChecks.KernelFi23M.hs.vld_q _ h1) (CertificateChecks.KernelFi23M.hs.vld_q _ h2)
  rw [h3, CertificateChecks.KernelFi23M.hs.one_mt] at e
  exact e.symm

noncomputable def Pu : GL (Fin 253) (ZMod 3) :=
  ⟨mat3 253 64009 (RS 120), mat3 253 64009 (RS 121), pc_mul, mul_eq_one_comm.1 pc_mul⟩

theorem conj_eq {X A : ℕ} (hX : CFSG.KD.Fi23M.VLD X = true) (hA : CFSG.KD.Fi23M.VLD A = true)
    (h : CFSG.KD.Fi23M.MUL (RS 120) X = CFSG.KD.Fi23M.MUL A (RS 120)) :
    mat3 253 64009 X = ((Pu⁻¹ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) *
      mat3 253 64009 A * (Pu : Matrix (Fin 253) (Fin 253) (ZMod 3)) := by
  have c120 := CertificateChecks.KernelFi23M.hs.vld_q _ pc_facts.1
  obtain ⟨-, e1⟩ := CertificateChecks.KernelFi23M.hs.mul_sound _ _ c120
    (CertificateChecks.KernelFi23M.hs.vld_q _ hX)
  obtain ⟨-, e2⟩ := CertificateChecks.KernelFi23M.hs.mul_sound _ _
    (CertificateChecks.KernelFi23M.hs.vld_q _ hA) c120
  rw [h, e2] at e1
  have hPi : ((Pu⁻¹ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) *
      (Pu : Matrix (Fin 253) (Fin 253) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc mat3 253 64009 X = (((Pu⁻¹ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) *
        (Pu : Matrix (Fin 253) (Fin 253) (ZMod 3))) * mat3 253 64009 X := by rw [hPi, Matrix.one_mul]
    _ = ((Pu⁻¹ : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) *
        ((Pu : Matrix (Fin 253) (Fin 253) (ZMod 3)) * mat3 253 64009 X) := Matrix.mul_assoc _ _ _
    _ = _ := by
        change _ * (mat3 253 64009 (RS 120) * mat3 253 64009 X) = _
        rw [← e1, ← Matrix.mul_assoc]
        rfl

theorem gen_mem {X A : ℕ} {k : ℕ} (hk : k < 120) (hXk : RS k = X)
    (hA : CFSG.KD.Fi23M.VLD A = true)
    (h : CFSG.KD.Fi23M.MUL (RS 120) X = CFSG.KD.Fi23M.MUL A (RS 120))
    {g : GL (Fin 253) (ZMod 3)} (hg : (g : Matrix (Fin 253) (Fin 253) (ZMod 3)) = mat3 253 64009 A) :
    Pu⁻¹ * g * Pu ∈ Sρ := by
  obtain ⟨u, hu, eu⟩ := slp_mem k hk
  have hX : CFSG.KD.Fi23M.VLD X = true := by rw [← hXk]; exact (slp_all k hk).1
  have : Pu⁻¹ * g * Pu = u := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hg, eu, hXk, conj_eq hX hA h]
  rw [this]
  exact hu

theorem vld_A23 : CFSG.KD.Fi23M.VLD (CFSG.KD.Fi23M.RB 1) = true := CertificateChecks.KernelFi23M.vld1

theorem vld_B23 : CFSG.KD.Fi23M.VLD (CFSG.KD.Fi23M.RB 2) = true := CertificateChecks.KernelFi23M.vld2

theorem conj_le : CFSG.Sporadic.Fi23.J.map (MulAut.conj Pu⁻¹).toMonoidHom ≤ Sρ := by
  have ha := Nat.eq_of_beq_eq_true pc_a
  have hb := Nat.eq_of_beq_eq_true pc_b
  rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact gen_mem (k := 31) (by norm_num) rfl vld_A23 ha
      (by change CFSG.Sporadic.Fi23.mA = _; rw [CertificateChecks.KernelFi23M.mA_eq])
  · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact gen_mem (k := 119) (by norm_num) rfl vld_B23 hb
      (by change CFSG.Sporadic.Fi23.mB = _; rw [CertificateChecks.KernelFi23M.mB_eq])

noncomputable abbrev Sst : Subgroup (stab (colSp Mb)) :=
  Subgroup.closure {⟨W1u, W1_stab⟩, ⟨W2u, W2_stab⟩}

theorem map_Sst : Sst.map ρ = Sρ := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]

theorem card_Sst : 4089470473293004800 ≤ Nat.card Sst := by
  rw [← CFSG.Sporadic.Fi23.card_J]
  calc Nat.card CFSG.Sporadic.Fi23.J =
      Nat.card (CFSG.Sporadic.Fi23.J.map (MulAut.conj Pu⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := (MulAut.conj Pu⁻¹).toMonoidHom)
          (MulAut.conj Pu⁻¹).injective).symm
    _ ≤ Nat.card Sρ := Subgroup.card_le_of_le conj_le
    _ = Nat.card (Sst.map ρ) := by rw [map_Sst]
    _ ≤ Nat.card Sst := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd Sst ρ)

end CertificateChecks.KernelFi24Orb

end
