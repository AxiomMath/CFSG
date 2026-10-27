module

public import Certificates.Kernel.W4Row.HS119Ind

public section

set_option maxRecDepth 4000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.HS119 CFSG.KS.SporSch
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CertificateChecks.KernelSporSch
  CFSG.KD.LQT.C4126

theorem letOK_cases {PA : ℕ → ℕ} {gout : ℕ} {inn : Bool} {c : ℕ} (h : letOK PA gout inn c = true) :
    (c < 2048 ∧ (inn = true → parK PA gout 9 (Nat.land c 1023) = 0)) ∨ aLetOK c = true := by
  have h' : Bool.rec (motive := fun _ => Bool) (aLetOK c)
      (impB inn (Nat.beq (parK PA gout 9 (Nat.land c 1023)) 0)) (Nat.blt c 2048) = true := h
  cases hb : Nat.blt c 2048
  · rw [hb] at h'
    exact Or.inr h'
  · rw [hb, impB_iff, beq_iff] at h'
    exact Or.inl ⟨Nat.blt_eq.mp hb, h'⟩

theorem witsOK_spec {Le : ℕ → ℕ → ℕ} {PA II : ℕ → ℕ} {gout b5 : ℕ} {inn : Bool} {X L W V : ℕ}
    (h : witsOK Le PA II gout b5 inn X L W V = true) :
    fd 8 L 0 ≤ 4 * fd 18 V 0 ∧ ∀ i < fd 18 V 0, witAt Le PA II gout b5 inn X W V i = true := by
  unfold witsOK at h
  rw [andB_iff, allN_iff] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, h.2⟩

theorem witAt_spec {Le : ℕ → ℕ → ℕ} {PA II : ℕ → ℕ} {gout b5 : ℕ} {inn : Bool} {X W V i : ℕ}
    (h : witAt Le PA II gout b5 inn X W V i = true) :
    Nat.land (fd 18 V (i + 1)) 255 < 192 ∧ X.testBit (Nat.land (fd 18 V (i + 1)) 255) = true ∧
      Nat.shiftRight (fd 18 V (i + 1)) 8 < 1024 ∧
      (inn = true → parK PA gout 9 (Nat.shiftRight (fd 18 V (i + 1)) 8) = 0) ∧
      (i + 1 < fd 18 V 0 →
        Nat.land (fd 18 V (i + 1)) 255 < Nat.land (fd 18 V (i + 1 + 1)) 255) ∧
      eq5 b5 (fun x => evW Le W (Le (II (Nat.land (fd 18 V (i + 1)) 255)) x))
        (fun x => Le (Nat.shiftRight (fd 18 V (i + 1)) 8) (evW Le W x)) = true := by
  unfold witAt at h
  rw [letB_eq, letB_eq, letB_eq, andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, letB_eq,
    bitB_iff, impB_iff, impB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨blt_iff.1 h1, h2, blt_iff.1 h3, fun hi => beq_iff.1 (h4 hi),
    fun hi => blt_iff.1 (h5 (blt_iff.2 hi)), h6⟩

theorem certAt_spec {Le : ℕ → ℕ → ℕ} {PA II A CH CW CV CY : ℕ → ℕ} {gout b5 : ℕ} {inn₀ : Bool}
    {s X L : ℕ} (h : certAt Le PA II A CH CW CV CY gout b5 inn₀ s X L = true) :
    (inn₀ = true → bitB (CH s) 3 = true) ∧
      (∀ i < Nat.land (CH s) 7,
        wordOK (letOK PA gout (bitB (CH s) 3)) (CW (Nat.add (Nat.mul 4 s) i)) = true ∧
        witsOK Le PA II gout b5 (bitB (CH s) 3) X L (CW (Nat.add (Nat.mul 4 s) i))
          (CV (Nat.add (Nat.mul 4 s) i)) = true) ∧
      ∀ t < 2, genOK Le PA II A CW gout b5 (bitB (CH s) 3) s (Nat.land (CH s) 7) X
        (CY (Nat.add (Nat.mul 2 s) t)) t = true := by
  unfold certAt at h
  rw [letB_eq, letB_eq, andB_iff, andB_iff, andB_iff, andB_iff, impB_iff, allN_iff,
    allN_iff] at h
  obtain ⟨-, -, h3, h4, h5⟩ := h
  refine ⟨h3, fun i hi => ?_, h5⟩
  have h4' := h4 i hi
  rw [letB_eq, andB_iff] at h4'
  exact h4'

theorem genOK_spec {Le : ℕ → ℕ → ℕ} {PA II A CW : ℕ → ℕ} {gout b5 : ℕ} {inn : Bool}
    {s m X Y t : ℕ} (h : genOK Le PA II A CW gout b5 inn s m X Y t = true) :
    wordOK (tokOK PA gout inn m X) Y = true ∧
      eq5 b5 (evW (tokE Le II CW s) Y) (fun x => fd 12 (A t) x) = true := by
  unfold genOK at h
  rw [andB_iff] at h
  exact h

theorem tokOK_lo {PA : ℕ → ℕ} {gout : ℕ} {inn : Bool} {m X tok : ℕ}
    (h : tokOK PA gout inn m X tok = true) (ht : tok < 1024) :
    inn = true → parK PA gout 9 tok = 0 := by
  have h' : Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt tok 2048) (andB (Nat.blt (Nat.shiftRight (Nat.sub tok 1024) 8) m)
        (andB (Nat.blt (Nat.land tok 255) 192) (bitB X (Nat.land tok 255)))))
      (impB inn (Nat.beq (parK PA gout 9 tok) 0)) (Nat.blt tok 1024) = true := h
  rw [blt_iff.2 ht, impB_iff] at h'
  exact fun hi => beq_iff.1 (h' hi)

theorem tokOK_hi {PA : ℕ → ℕ} {gout : ℕ} {inn : Bool} {m X tok : ℕ}
    (h : tokOK PA gout inn m X tok = true) (ht : ¬ tok < 1024) :
    tok < 2048 ∧ Nat.shiftRight (Nat.sub tok 1024) 8 < m ∧ Nat.land tok 255 < 192 ∧
      X.testBit (Nat.land tok 255) = true := by
  have h' : Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt tok 2048) (andB (Nat.blt (Nat.shiftRight (Nat.sub tok 1024) 8) m)
        (andB (Nat.blt (Nat.land tok 255) 192) (bitB X (Nat.land tok 255)))))
      (impB inn (Nat.beq (parK PA gout 9 tok) 0)) (Nat.blt tok 1024) = true := h
  rw [blt_false (Nat.le_of_not_lt ht), andB_iff, andB_iff, andB_iff, blt_iff, blt_iff, blt_iff,
    bitB_iff] at h'
  exact h'

theorem tokE_lo {Le : ℕ → ℕ → ℕ} {II CW : ℕ → ℕ} {s tok : ℕ} (ht : tok < 1024) :
    tokE Le II CW s tok = Le tok := by
  funext x
  change Bool.rec (motive := fun _ => ℕ) _ (Le tok x) (Nat.blt tok 1024) = _
  rw [blt_iff.2 ht]

theorem tokE_hi {Le : ℕ → ℕ → ℕ} {II CW : ℕ → ℕ} {s tok : ℕ} (ht : ¬ tok < 1024) :
    tokE Le II CW s tok = fun x =>
      evW Le (CW (Nat.add (Nat.mul 4 s) (Nat.shiftRight (Nat.sub tok 1024) 8)))
        (Le (II (Nat.land tok 255))
          (evWI Le (CW (Nat.add (Nat.mul 4 s) (Nat.shiftRight (Nat.sub tok 1024) 8))) x)) := by
  funext x
  change Bool.rec (motive := fun _ => ℕ)
    (letN (CW (Nat.add (Nat.mul 4 s) (Nat.shiftRight (Nat.sub tok 1024) 8))) fun W =>
      letN (II (Nat.land tok 255)) fun ea => evW Le W (Le ea (evWI Le W x)))
    (Le tok x) (Nat.blt tok 1024) = _
  rw [blt_false (Nat.le_of_not_lt ht), letN_eq, letN_eq]

theorem hasOut_of {PA II : ℕ → ℕ} {gout L : ℕ}
    (h : ∃ i < fd 8 L 0, parK PA gout 9 (II (fd 8 L (i + 1))) ≠ 0) : hasOut PA II gout L = true := by
  unfold hasOut
  rw [anyN_iff]
  obtain ⟨i, hi, h⟩ := h
  refine ⟨i, hi, ?_⟩
  rw [notB_iff, beq_iff]
  exact h

theorem strict_inj {a : ℕ → ℕ} {n : ℕ} (h : ∀ i, i + 1 < n → a i < a (i + 1)) :
    ∀ i < n, ∀ j < n, a i = a j → i = j := by
  have mono : ∀ i j, i < j → j < n → a i < a j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih h' (by omega)).trans (h j hj)
      · exact h i hj
  intro i hi j hj hij
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd hij (mono i j h' hj).ne
  · exact h'
  · exact absurd hij (mono j i h' hi).ne'

theorem le_card_of_inj {H : Subgroup (Equiv.Perm (Fin 3850))} {n : ℕ}
    {f : ℕ → Equiv.Perm (Fin 3850)} (hf : ∀ i < n, f i ∈ H)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ Nat.card H := by
  classical
  have h1 : ((Finset.range n).image f).card = n := by
    rw [Finset.card_image_of_injOn fun i hi j hj h =>
      hinj i (by simpa using hi) j (by simpa using hj) h, Finset.card_range]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  calc n = ((Finset.range n).image f).card := h1.symm
    _ = (((Finset.range n).image f : Finset _) : Set (Equiv.Perm (Fin 3850))).ncard :=
      (Set.ncard_coe_finset _).symm
    _ ≤ (H : Set (Equiv.Perm (Fin 3850))).ncard := by
      refine Set.ncard_le_ncard (fun x hx => ?_) (Set.toFinite _)
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact hf i (by simpa using hi)

theorem card_le_of_cover {H : Subgroup (Equiv.Perm (Fin 3850))} {n : ℕ}
    {f : ℕ → Equiv.Perm (Fin 3850)} (h : ∀ x ∈ H, ∃ i < n, x = f i) : Nat.card H ≤ n := by
  classical
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  calc (H : Set (Equiv.Perm (Fin 3850))).ncard
      ≤ (((Finset.range n).image f : Finset _) : Set (Equiv.Perm (Fin 3850))).ncard := by
        refine Set.ncard_le_ncard (fun x hx => ?_) (Finset.finite_toSet _)
        obtain ⟨i, hi, rfl⟩ := h x hx
        exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩)
    _ = ((Finset.range n).image f).card := Set.ncard_coe_finset _
    _ ≤ n := Finset.card_image_le.trans (Finset.card_range n).le

theorem map_conj_map_conj (A : Subgroup (Equiv.Perm (Fin 3850))) (g σ : Equiv.Perm (Fin 3850)) :
    (A.map (MulAut.conj σ).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * σ)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem card_map_conj (A : Subgroup (Equiv.Perm (Fin 3850))) (g : Equiv.Perm (Fin 3850)) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem xor_parts {c : ℕ} :
    Nat.land (Nat.xor c 1024) 1023 = Nat.land c 1023 ∧
      Nat.shiftRight (Nat.xor c 1024) 10 = Nat.xor (Nat.shiftRight c 10) 1 := by
  constructor
  · change (c ^^^ 1024) &&& (2 ^ 10 - 1) = c &&& (2 ^ 10 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.xor_mod_two_pow]
    norm_num
  · change (c ^^^ 1024) >>> 10 = (c >>> 10) ^^^ 1
    rw [Nat.shiftRight_xor_distrib]
    rfl

theorem let_lt {PA : ℕ → ℕ} {gout : ℕ} {inn : Bool} {c : ℕ} (h : letOK PA gout inn c = true) :
    c < 4096 ∧ (2 ≤ Nat.shiftRight c 10 → Nat.land c 1023 < 2) := by
  rcases letOK_cases h with ⟨hc, -⟩ | ha
  · refine ⟨by omega, fun h2 => ?_⟩
    change 2 ≤ c >>> 10 at h2
    rw [Nat.shiftRight_eq_div_pow] at h2
    omega
  · obtain ⟨ht, hv⟩ := aLet_parts ha
    refine ⟨?_, fun _ => hv⟩
    have ht' : c >>> 10 ≤ 3 := by
      change Nat.shiftRight c 10 ≤ 3
      omega
    rw [Nat.shiftRight_eq_div_pow] at ht'
    omega

theorem xor_cond {c : ℕ} (hc : c < 4096) (h : 2 ≤ Nat.shiftRight c 10 → Nat.land c 1023 < 2) :
    2 ≤ Nat.shiftRight (Nat.xor c 1024) 10 → Nat.land (Nat.xor c 1024) 1023 < 2 := by
  rw [xor_parts.1, xor_parts.2]
  intro h2
  apply h
  have h4 : Nat.shiftRight c 10 < 4 := by
    change c >>> 10 < 4
    rw [Nat.shiftRight_eq_div_pow]
    omega
  generalize Nat.shiftRight c 10 = t at h4 h2 ⊢
  interval_cases t <;> revert h2 <;> decide

section HS


theorem lE_inv_rep {c : ℕ} (hc : c < 4096) (h : 2 ≤ Nat.shiftRight c 10 → Nat.land c 1023 < 2) :
    RepF 3850 (evH (Nat.xor c 1024)) (lE c)⁻¹ := by
  have h' := evH_rep (xor_cond hc h)
  have hx : (lE c)⁻¹ = lE (Nat.xor c 1024) := (letE_xor e hsGen hc).symm
  rw [hx]
  exact h'

theorem lE_memK {inn : Bool} {c : ℕ} (h : letOK SPA (GO 0) inn c = true)
    {K : Subgroup (Equiv.Perm (Fin 3850))} (hPK : hsP ≤ K) (hRK : inn = false → hsR ≤ K) :
    lE c ∈ K := by
  rcases letOK_cases h with ⟨hc, hinn⟩ | ha
  · have hv := land1023_lt c
    have hek : e (Nat.land c 1023) ∈ K := by
      cases hi : inn
      · exact hRK hi (e_memR hv)
      · exact hPK ((e_mem_iff hv).2 (hinn hi))
    have ht : Nat.shiftRight c 10 < 2 := by
      change c >>> 10 < 2
      rw [Nat.shiftRight_eq_div_pow]
      omega
    unfold lE letE
    have ht2 : Nat.shiftRight c 10 = 0 ∨ Nat.shiftRight c 10 = 1 := by omega
    rcases ht2 with ht | ht
    · rw [if_pos ht]
      exact hek
    · rw [if_neg (by omega), if_pos ht]
      exact K.inv_mem hek
  · exact hPK (lE_memP ha)

theorem wC_rep {inn : Bool} {W : ℕ} (h : wordOK (letOK SPA (GO 0) inn) W = true) :
    RepF 3850 (evW evH W) (wA W) :=
  evW_rep fun i hi => evH_rep (let_lt (wordOK_spec h i hi)).2

theorem wCI_rep {inn : Bool} {W : ℕ} (h : wordOK (letOK SPA (GO 0) inn) W = true) :
    RepF 3850 (evWI evH W) (wA W)⁻¹ :=
  evWI_rep fun i hi => lE_inv_rep (let_lt (wordOK_spec h i hi)).1 (let_lt (wordOK_spec h i hi)).2

theorem wC_memK {inn : Bool} {W : ℕ} (h : wordOK (letOK SPA (GO 0) inn) W = true)
    {K : Subgroup (Equiv.Perm (Fin 3850))} (hPK : hsP ≤ K) (hRK : inn = false → hsR ≤ K) :
    wA W ∈ K :=
  wE_mem (fun i hi => lE_memK (wordOK_spec h i hi) hPK hRK) _ le_rfl

theorem conj_memP_iff {g x : Equiv.Perm (Fin 3850)} (hg : g ∈ hsR) (hx : x ∈ hsR) :
    g * x * g⁻¹ ∈ hsP ↔ x ∈ hsP := by
  rw [mul_memP_iff (hsR.mul_mem hg hx) (hsR.inv_mem hg), mul_memP_iff hg hx]
  have hi : g⁻¹ ∈ hsP ↔ g ∈ hsP := ⟨fun h => by simpa using hsP.inv_mem h, hsP.inv_mem⟩
  rw [hi]
  by_cases h1 : g ∈ hsP <;> by_cases h2 : x ∈ hsP <;> simp only [h1, h2, iff_true, iff_false,
    true_iff, false_iff, not_true_eq_false, not_false_eq_true]

theorem e_memC {inn : Bool} {k : ℕ} (hk : k < 1024) (hinn : inn = true → parK SPA (GO 0) 9 k = 0)
    {C : Subgroup (Equiv.Perm (Fin 3850))} (hPC : hsS ⊓ hsP ≤ C) (hSC : inn = false → hsS ≤ C) :
    e k ∈ C := by
  cases hi : inn
  · exact hSC hi (e_memS hk)
  · exact hPC ⟨e_memS hk, (e_mem_iff hk).2 (hinn hi)⟩

theorem hsP_le_of_slot {inn₀ : Bool} {s X L : ℕ}
    (hcert : certAt evH SPA II HS.F CH CW CV CY (GO 0) (HZ 1) inn₀ s X L = true)
    (hXL : ∀ b, X.testBit b = true → ∃ i < fd 8 L 0, fd 8 L (i + 1) = b)
    {K A C : Subgroup (Equiv.Perm (Fin 3850))} (hPK : hsP ≤ K)
    (hRK : bitB (CH s) 3 = false → hsR ≤ K)
    (hA : ∀ b < 192, (X.testBit b = true ↔ ι b ∈ A)) (hAι : ∀ x ∈ A, ∃ b < 192, x = ι b)
    (hPC : hsS ⊓ hsP ≤ C) (hSC : bitB (CH s) 3 = false → hsS ≤ C)
    (hcl : ∀ g ∈ K, Nat.card A ≤ 4 * Nat.card ↥(A.map (MulAut.conj g).toMonoidHom ⊓ C) →
      A.map (MulAut.conj g).toMonoidHom ≤ C) :
    hsP ≤ C := by
  obtain ⟨-, hW, hY⟩ := certAt_spec hcert
  have hcardA : Nat.card A ≤ fd 8 L 0 := by
    refine card_le_of_cover (f := fun i => ι (fd 8 L (i + 1))) fun x hx => ?_
    obtain ⟨b, hb, rfl⟩ := hAι x hx
    obtain ⟨i, hi, hib⟩ := hXL b ((hA b hb).2 hx)
    exact ⟨i, hi, by rw [hib]⟩
  have hsub : ∀ i < Nat.land (CH s) 7,
      A.map (MulAut.conj (wA (CW (Nat.add (Nat.mul 4 s) i)))).toMonoidHom ≤ C := by
    intro i hi
    obtain ⟨hw, hv⟩ := hW i hi
    obtain ⟨hq, hwit⟩ := witsOK_spec hv
    generalize CW (Nat.add (Nat.mul 4 s) i) = W at hw hwit ⊢
    generalize CV (Nat.add (Nat.mul 4 s) i) = V at hq hwit ⊢
    have hgR : wA W ∈ hsR := wC_memK hw HS72.P_le_R fun _ => le_rfl
    refine hcl _ (wC_memK hw hPK hRK) ?_
    have hmem : ∀ i' < fd 18 V 0, wA W * ι (Nat.land (fd 18 V (i' + 1)) 255) * (wA W)⁻¹ ∈
        A.map (MulAut.conj (wA W)).toMonoidHom ⊓ C := by
      intro i' hi'
      obtain ⟨ha, hbit, hk, hinn, -, h5⟩ := witAt_spec (hwit i' hi')
      have hka := (ii_parts ha).1
      have heq := eqR5 ((wC_rep hw).comp (evH_small hka)) ((evH_small hk).comp (wC_rep hw))
        (hsR.mul_mem hgR (e_memR hka)) (hsR.mul_mem (e_memR hk) hgR) h5
      refine ⟨map_conj_mem.2 ?_, ?_⟩
      · rw [show (wA W)⁻¹ * (wA W * ι (Nat.land (fd 18 V (i' + 1)) 255) * (wA W)⁻¹) * wA W =
          ι (Nat.land (fd 18 V (i' + 1)) 255) by group]
        exact (hA _ ha).1 hbit
      · change wA W * e (II (Nat.land (fd 18 V (i' + 1)) 255)) * (wA W)⁻¹ ∈ C
        rw [heq, mul_inv_cancel_right]
        exact e_memC hk hinn hPC hSC
    have hle : fd 18 V 0 ≤ Nat.card ↥(A.map (MulAut.conj (wA W)).toMonoidHom ⊓ C) := by
      refine le_card_of_inj hmem fun i hi j hj hij => ?_
      have hai := (witAt_spec (hwit i hi)).1
      have haj := (witAt_spec (hwit j hj)).1
      have h1 : ι (Nat.land (fd 18 V (i + 1)) 255) = ι (Nat.land (fd 18 V (j + 1)) 255) := by
        simpa using hij
      exact strict_inj (a := fun i => Nat.land (fd 18 V (i + 1)) 255)
        (fun i hi => (witAt_spec (hwit i (by omega))).2.2.2.2.1 hi) i hi j hj (ι_inj hai haj h1)
    calc Nat.card A ≤ fd 8 L 0 := hcardA
      _ ≤ 4 * fd 18 V 0 := hq
      _ ≤ _ := Nat.mul_le_mul_left 4 hle
  have hgen : ∀ t < 2, hsGen t ∈ C := by
    intro t ht
    obtain ⟨hYw, hY5⟩ := genOK_spec (hY t ht)
    generalize CY (Nat.add (Nat.mul 2 s) t) = Y at hYw hY5
    let tokEl : ℕ → Equiv.Perm (Fin 3850) := fun tok => if tok < 1024 then e tok else
      wA (CW (Nat.add (Nat.mul 4 s) (Nat.shiftRight (Nat.sub tok 1024) 8))) *
        ι (Nat.land tok 255) *
        (wA (CW (Nat.add (Nat.mul 4 s) (Nat.shiftRight (Nat.sub tok 1024) 8))))⁻¹
    have htok : ∀ i < fd 12 Y 0, RepF 3850 (tokE evH II CW s (fd 12 Y (i + 1)))
        (tokEl (fd 12 Y (i + 1))) ∧ tokEl (fd 12 Y (i + 1)) ∈ C ∧
        tokEl (fd 12 Y (i + 1)) ∈ hsR := by
      intro i hi
      have hok := wordOK_spec hYw i hi
      generalize fd 12 Y (i + 1) = tok at hok ⊢
      by_cases hlt : tok < 1024
      · have e1 : tokEl tok = e tok := if_pos hlt
        rw [e1, tokE_lo hlt]
        exact ⟨evH_small hlt, e_memC hlt (tokOK_lo hok hlt) hPC hSC, e_memR hlt⟩
      · obtain ⟨-, him, ha, hbit⟩ := tokOK_hi hok hlt
        obtain ⟨hw, -⟩ := hW _ him
        generalize hWd : CW (Nat.add (Nat.mul 4 s) (Nat.shiftRight (Nat.sub tok 1024) 8)) = W
          at hw
        have e1 : tokEl tok = wA W * ι (Nat.land tok 255) * (wA W)⁻¹ := by
          change (if tok < 1024 then _ else _) = _
          rw [if_neg hlt, hWd]
        have hka := (ii_parts ha).1
        have hgR : wA W ∈ hsR := wC_memK hw HS72.P_le_R fun _ => le_rfl
        rw [e1, tokE_hi hlt, hWd]
        refine ⟨?_, ?_, hsR.mul_mem (hsR.mul_mem hgR (e_memR hka)) (hsR.inv_mem hgR)⟩
        · have hr := (wC_rep hw).comp ((evH_small hka).comp (wCI_rep hw))
          rw [← mul_assoc] at hr
          exact hr
        · have hsubW := hsub _ him
          rw [hWd] at hsubW
          refine hsubW (map_conj_mem.2 ?_)
          rw [show (wA W)⁻¹ * (wA W * ι (Nat.land tok 255) * (wA W)⁻¹) * wA W =
            ι (Nat.land tok 255) by group]
          exact (hA _ ha).1 hbit
    have hrep : RepF 3850 (evW (tokE evH II CW s) Y) (wE tokEl Y (fd 12 Y 0)) :=
      evW_rep fun i hi => (htok i hi).1
    have hwR : wE tokEl Y (fd 12 Y 0) ∈ hsR := wE_mem (fun i hi => (htok i hi).2.2) _ le_rfl
    have hwC : wE tokEl Y (fd 12 Y 0) ∈ C := wE_mem (fun i hi => (htok i hi).2.1) _ le_rfl
    have hgR : hsGen t ∈ hsR := by
      refine HS72.P_le_R ?_
      rw [hsP]
      refine Subgroup.subset_closure ?_
      interval_cases t <;> simp
    rw [← eqR5 hrep (a_rep ht).1 hwR hgR hY5]
    exact hwC
  rw [hsP, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hgen 0 (by norm_num)
  · exact hgen 1 (by norm_num)

theorem hsR_le_of_out {R' : Subgroup (Equiv.Perm (Fin 3850))} (hPR : hsP ≤ R')
    {a : Equiv.Perm (Fin 3850)} (ha : a ∈ R') (haR : a ∈ hsR) (haP : a ∉ hsP) : hsR ≤ R' := by
  intro r hr
  by_cases hrP : r ∈ hsP
  · exact hPR hrP
  · have h1 : a * r ∈ hsP := (mul_memP_iff haR hr).2 (iff_of_false haP hrP)
    have h2 := R'.mul_mem (R'.inv_mem ha) (hPR h1)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2

theorem rep_facts {A : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS)
    (hA2 : ∀ a ∈ A, a * a = 1) {g : Equiv.Perm (Fin 3850)} (hg : g ∈ hsS) {X : ℕ}
    (h : ∀ b < 192, (X.testBit b = true ↔ g⁻¹ * ι b * g ∈ A)) :
    (∀ b < 192, (X.testBit b = true ↔ ι b ∈ A.map (MulAut.conj g).toMonoidHom)) ∧
      ∀ x ∈ A.map (MulAut.conj g).toMonoidHom, ∃ b < 192, x = ι b := by
  refine ⟨fun b hb => by rw [h b hb, map_conj_mem], fun x hx => ?_⟩
  have hx' := map_conj_mem.1 hx
  have e1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  have hxS : x ∈ hsS := by
    rw [e1]
    exact hsS.mul_mem (hsS.mul_mem hg (hAS hx')) (hsS.inv_mem hg)
  have hsq : x * x = 1 := by
    rw [e1]
    calc g * (g⁻¹ * x * g) * g⁻¹ * (g * (g⁻¹ * x * g) * g⁻¹) =
        g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [hA2 _ hx', mul_one, mul_inv_cancel]
  exact exists_ι hxS hsq

theorem hs119_core {R' : Subgroup (Equiv.Perm (Fin 3850))} (hPR : hsP ≤ R') (hRR : R' ≤ hsR)
    {A C : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS ⊓ R') (hA2 : ∀ a ∈ A, a * a = 1)
    (hA8 : 8 ≤ Nat.card A) (hSC : hsS ⊓ R' ≤ C)
    (hcl : ∀ g ∈ R', Nat.card A ≤ 4 * Nat.card ↥(A.map (MulAut.conj g).toMonoidHom ⊓ C) →
      A.map (MulAut.conj g).toMonoidHom ≤ C) :
    R' ≤ C := by
  have hAS' : A ≤ hsS := hAS.trans inf_le_left
  have hAR : A ≤ R' := hAS.trans inf_le_right
  have hPC : hsS ⊓ hsP ≤ C := fun x hx => hSC ⟨hx.1, hPR hx.2⟩
  have htrans : ∀ g ∈ R', ∀ g' ∈ R',
      Nat.card (A.map (MulAut.conj g).toMonoidHom) ≤ 4 * Nat.card ↥((A.map
        (MulAut.conj g).toMonoidHom).map (MulAut.conj g').toMonoidHom ⊓ C) →
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g').toMonoidHom ≤ C := by
    intro g hg g' hg' hq
    rw [map_conj_map_conj] at hq ⊢
    rw [card_map_conj] at hq
    exact hcl _ (R'.mul_mem hg' hg) hq
  have h8 : ∀ {X L : ℕ} {g : Equiv.Perm (Fin 3850)},
      (∀ b, X.testBit b = true → ∃ i < fd 8 L 0, fd 8 L (i + 1) = b) →
      (∀ b < 192, (X.testBit b = true ↔ ι b ∈ A.map (MulAut.conj g).toMonoidHom)) →
      (∀ x ∈ A.map (MulAut.conj g).toMonoidHom, ∃ b < 192, x = ι b) → 8 ≤ fd 8 L 0 := by
    intro X L g hXL hA' hAι
    refine hA8.trans ?_
    rw [← card_map_conj A g]
    refine card_le_of_cover (f := fun i => ι (fd 8 L (i + 1))) fun x hx => ?_
    obtain ⟨b, hb, rfl⟩ := hAι x hx
    obtain ⟨i, hi, hib⟩ := hXL b ((hA' b hb).2 hx)
    exact ⟨i, hi, by rw [hib]⟩
  have hPle : hsP ≤ C := by
    by_cases hAP : A ≤ hsP
    · obtain ⟨j, hj, g, hg, hgP, h⟩ := clsP hAS' hAP hA2
      obtain ⟨hA', hAι⟩ := rep_facts hAS' hA2 hg h
      obtain ⟨hLb, -⟩ := ls_parts ((allN_iff _ _).1 (andB_iff.1 x_ls).2 j hj)
        ((allN_iff _ _).1 (andB_iff.1 c_inc).2 j hj)
      have hXL : ∀ b, (RP j).testBit b = true → ∃ i < fd 8 (LP j) 0, fd 8 (LP j) (i + 1) = b :=
        fun b hb => (hLb b).1 hb
      have hslot := (allN_iff _ _).1 c_p j hj
      unfold slotP at hslot
      rw [impB_iff] at hslot
      have hcert := hslot (Nat.ble_eq_true_of_le (h8 hXL hA' hAι))
      have hb3 := (certAt_spec hcert).1 rfl
      have hno : ∀ {P : Prop}, bitB (CH (Nat.add 266 j)) 3 = false → P := fun hf =>
        absurd (hb3.symm.trans hf) (by decide)
      exact hsP_le_of_slot hcert hXL hPR hno hA' hAι hPC hno (htrans g (hPR hgP))
    · obtain ⟨a, haA, haP⟩ := Set.not_subset.1 hAP
      have hRle := hsR_le_of_out hPR (hAR haA) (hRR (hAR haA)) haP
      have hSS : hsS ≤ C := fun x hx => hSC ⟨hx, hRle (HS72.S_le_R hx)⟩
      obtain ⟨j, hj, g, hg, h⟩ := clsS hAS' hA2
      obtain ⟨hA', hAι⟩ := rep_facts hAS' hA2 hg h
      obtain ⟨hLb, -⟩ := ls_parts ((allN_iff _ _).1 (andB_iff.1 x_ls).1 j hj)
        ((allN_iff _ _).1 (andB_iff.1 c_inc).1 j hj)
      have hXL : ∀ b, (RS j).testBit b = true → ∃ i < fd 8 (LS j) 0, fd 8 (LS j) (i + 1) = b :=
        fun b hb => (hLb b).1 hb
      have hout : hasOut SPA II (GO 0) (LS j) = true := by
        refine hasOut_of ?_
        have hgaS : g * a * g⁻¹ ∈ hsS := hsS.mul_mem (hsS.mul_mem hg (hAS' haA)) (hsS.inv_mem hg)
        have hgsq : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
          calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
            _ = 1 := by rw [hA2 a haA, mul_one, mul_inv_cancel]
        obtain ⟨b, hb, hbe⟩ := exists_ι hgaS hgsq
        have hbA : g⁻¹ * ι b * g ∈ A := by
          rw [← hbe]
          simpa [mul_assoc] using haA
        obtain ⟨i, hi, hib⟩ := hXL b ((h b hb).2 hbA)
        refine ⟨i, hi, fun h0 => haP ?_⟩
        rw [hib] at h0
        have hP : ι b ∈ hsP := (e_mem_iff (ii_parts hb).1).2 h0
        rw [← hbe] at hP
        exact (conj_memP_iff (HS72.S_le_R hg) (hRR (hAR haA))).1 hP
      have hslot : slotS evH SPA II HS.F CH CW CV CY RS LS (GO 0) (HZ 1) j = true := by
        have hr := fun {lo cnt : ℕ} (h : CFSG.KC.Misc.Clos.allR lo cnt
            (slotS evH SPA II HS.F CH CW CV CY RS LS (GO 0) (HZ 1)) = true) (h1 : lo ≤ j)
            (h2 : j < lo + cnt) => (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 h j h1 h2
        rcases Nat.lt_or_ge j 150 with h' | h'
        · exact hr c_s0 (by omega) (by omega)
        rcases Nat.lt_or_ge j 200 with h'' | h''
        · exact hr c_s1 h' (by omega)
        · exact hr c_s2 h'' (by omega)
      unfold slotS at hslot
      rw [impB_iff, andB_iff] at hslot
      have hcert := hslot ⟨Nat.ble_eq_true_of_le (h8 hXL hA' hAι), hout⟩
      exact hsP_le_of_slot hcert hXL hPR (fun _ => hRle) hA' hAι hPC (fun _ => hSS)
        (htrans g (hRle (HS72.S_le_R hg)))
  intro r hr
  by_cases hrP : r ∈ hsP
  · exact hPle hrP
  · have hRle := hsR_le_of_out hPR hr (hRR hr) hrP
    have hz := z_parts.1
    have hzR := e_memR hz
    have h1 : (e (HZ 0))⁻¹ * r ∈ hsP := by
      refine (mul_memP_iff (hsR.inv_mem hzR) (hRR hr)).2 ?_
      have hzi : (e (HZ 0))⁻¹ ∉ hsP := fun h => ez_notMem (by simpa using hsP.inv_mem h)
      exact iff_of_false hzi hrP
    have h2 := C.mul_mem (hSC ⟨e_memS hz, hRle hzR⟩) (hPle h1)
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at h2

end HS

end CFSG.KD.HS119

end
