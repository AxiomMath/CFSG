module

public import Certificates.Kernel.ThCent.LGlue
public import Certificates.Kernel.ThPump.Chk
public import CFSG.Certificates.Kernel.ThPump.Sound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive

public section

namespace CertificateChecks.KernelThPump

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KC.ThCent CFSG.KC.ThPump CFSG.KD.ThCent.L CFSG.KD.ThPump
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative CertificateChecks.KernelThList
  CFSG.KD

set_option maxRecDepth 100000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem card_inf_centralizer_le_of_orbit {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    {t₀ : G} (ht₀C : t₀ ∈ C) (ht₀ : orderOf t₀ = 3) (hC : Nat.card C = 3000) (u : Fin 100 → G)
    (huC : ∀ k, u k ∈ C) (hinj : ∀ k l, u k * t₀ * (u k)⁻¹ = u l * t₀ * (u l)⁻¹ → k = l)
    {t : G} (htC : t ∈ C) (ht : orderOf t = 3) :
    Nat.card ↥(C ⊓ Subgroup.centralizer ({t} : Set G)) ≤ 30 := by
  have hA : 100 * Nat.card ↥(C ⊓ Subgroup.centralizer ({t₀} : Set G)) ≤ Nat.card C := by
    let F : Fin 100 × ↥(C ⊓ Subgroup.centralizer ({t₀} : Set G)) → ↥C := fun p =>
      ⟨u p.1 * p.2, C.mul_mem (huC p.1) (Subgroup.mem_inf.1 p.2.2).1⟩
    have hF : Function.Injective F := by
      rintro ⟨k, s⟩ ⟨l, s'⟩ h
      have h1 : u k * (s : G) = u l * (s' : G) := congrArg Subtype.val h
      have hs : (s : G) * t₀ = t₀ * s :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).2
      have hs' : (s' : G) * t₀ = t₀ * s' :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s'.2).2
      have hsi : (s : G)⁻¹ * t₀ = t₀ * (s : G)⁻¹ := by
        calc (s : G)⁻¹ * t₀ = (s : G)⁻¹ * (t₀ * s) * (s : G)⁻¹ := by group
          _ = (s : G)⁻¹ * (s * t₀) * (s : G)⁻¹ := by rw [hs]
          _ = t₀ * (s : G)⁻¹ := by group
      have e : u k = u l * s' * (s : G)⁻¹ := by
        rw [← h1]
        group
      have hkl : k = l := hinj k l (by
        rw [e]
        calc u l * s' * (s : G)⁻¹ * t₀ * (u l * s' * (s : G)⁻¹)⁻¹
            = u l * s' * ((s : G)⁻¹ * t₀) * s * (s' : G)⁻¹ * (u l)⁻¹ := by group
          _ = u l * ((s' : G) * t₀) * (s' : G)⁻¹ * (u l)⁻¹ := by
            rw [hsi]
            group
          _ = u l * t₀ * (u l)⁻¹ := by
            rw [hs']
            group)
      subst hkl
      have : (s : G) = s' := mul_left_cancel h1
      exact Prod.ext rfl (Subtype.ext this)
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_prod, Nat.card_fin] at this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQC : Subgroup.zpowers t₀ ≤ C := (Subgroup.zpowers_le).2 ht₀C
  have h3000 : (3000 : ℕ) = 3 ^ 1 * 1000 := by norm_num
  have hfac : (Nat.card C).factorization 3 = 1 := by
    rw [hC, h3000, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.prime_three.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hQ : Nat.card (Subgroup.zpowers t₀) = 3 ^ (Nat.card C).factorization 3 := by
    rw [Nat.card_zpowers, ht₀, hfac, pow_one]
  obtain ⟨g, hgC, hgt⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQC hQ htC ht
  have ht' : orderOf (g⁻¹ * t * g) = 3 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    rw [this, ht]
  have hzeq : Subgroup.zpowers (g⁻¹ * t * g) = Subgroup.zpowers t₀ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hgt)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ht', ht₀])
  have ht₀mem : t₀ ∈ Subgroup.zpowers (g⁻¹ * t * g) := by
    rw [hzeq]
    exact Subgroup.mem_zpowers t₀
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ht₀mem
  have hcen : Subgroup.centralizer ({g⁻¹ * t * g} : Set G) ≤
      Subgroup.centralizer ({t₀} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hc : Commute x (g⁻¹ * t * g) := hx
    rw [← hn]
    exact (hc.zpow_right n)
  have hB : Nat.card ↥(C ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card ↥(C ⊓ Subgroup.centralizer ({g⁻¹ * t * g} : Set G)) := by
    let F : ↥(C ⊓ Subgroup.centralizer ({t} : Set G)) →
        ↥(C ⊓ Subgroup.centralizer ({g⁻¹ * t * g} : Set G)) := fun x =>
      ⟨g⁻¹ * x * g, by
        obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 x.2
        have hxt : (x : G) * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hx2
        refine Subgroup.mem_inf.2 ⟨C.mul_mem (C.mul_mem (C.inv_mem hgC) hx1) hgC, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc g⁻¹ * (x : G) * g * (g⁻¹ * t * g) = g⁻¹ * ((x : G) * t) * g := by group
          _ = g⁻¹ * (t * x) * g := by rw [hxt]
          _ = g⁻¹ * t * g * (g⁻¹ * x * g) := by group⟩
    have hF : Function.Injective F := by
      intro x y h
      have h1 : g⁻¹ * (x : G) * g = g⁻¹ * y * g := congrArg Subtype.val h
      exact Subtype.ext (by simpa using h1)
    exact Nat.card_le_card_of_injective F hF
  have hle := Subgroup.card_le_of_le (inf_le_inf_left C hcen)
  omega


local notation "R5" => slpJ a b prog5

local notation "c5" => R5 94 * R5 105 * R5 94 ^ 4 * R5 105 ^ 4

abbrev IsLetter (r : ℕ) : Prop := r = 19 ∨ r = 99 ∨ r = 114 ∨ r = 115

theorem mat_letter {r : ℕ} (hr : IsLetter r) : 𝕄 (R5 r) = pkMat (V5 r) :=
  mat_R5 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)

theorem mat_c5 : 𝕄 c5 = pkMat C5 := by
  obtain ⟨-, -, -, hk⟩ := CertificateChecks.KernelThCent.fwd_mats
  have hx := mat_R5 94 (by decide)
  have hy := mat_R5 105 (by decide)
  unfold C5
  rw [mat_mul, mat_mul, mat_mul, mat_pow, mat_pow, hx, hy, pkMat_mulB hk, pkMat_mulB hk,
    pkMat_mulB hk, pkMat_powB hk _ _ 3 (by norm_num), pkMat_powB hk _ _ 3 (by norm_num)]

theorem letter_comm {r : ℕ} (hr : IsLetter r) : R5 r * c5 = c5 * R5 r := by
  obtain ⟨-, -, -, hk⟩ := CertificateChecks.KernelThCent.fwd_mats
  have key : Nat.beq (mulB ThS.c ThS.rm (V5 r) C5) (mulB ThS.c ThS.rm C5 (V5 r)) = true := by
    rcases hr with rfl | rfl | rfl | rfl
    · exact comm_19
    · exact comm_99
    · exact comm_114
    · exact comm_115
  refine mat_inj ?_
  rw [mat_mul (R5 r) c5, mat_mul c5 (R5 r), mat_letter hr, mat_c5, ← pkMat_mulB hk,
    ← pkMat_mulB hk,
    Nat.eq_of_beq_eq_true key]

theorem mat_letter_inv {r e : ℕ} (hr : IsLetter r)
    (key : Nat.beq (mulB ThS.c ThS.rm (V5 r) (invL r e)) ThS.ONE = true) :
    𝕄 ((R5 r)⁻¹) = pkMat (invL r e) := by
  obtain ⟨-, -, -, hk⟩ := CertificateChecks.KernelThCent.fwd_mats
  refine mat_inv_eq ?_
  rw [mat_letter hr, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true key, pkMat_one hk]

theorem selL_19 (a b c d : ℕ) : selL a b c d 19 = a := rfl
theorem selL_99 (a b c d : ℕ) : selL a b c d 99 = b := rfl
theorem selL_114 (a b c d : ℕ) : selL a b c d 114 = c := rfl
theorem selL_115 (a b c d : ℕ) : selL a b c d 115 = d := rfl

theorem selL_letter {r : ℕ} (hr : IsLetter r) :
    pkMat (selL (V5 19) (V5 99) (V5 114) (V5 115) r) = 𝕄 (R5 r) := by
  rw [mat_letter hr]
  rcases hr with rfl | rfl | rfl | rfl
  · rw [selL_19]
  · rw [selL_99]
  · rw [selL_114]
  · rw [selL_115]

theorem selL_letter_inv {r : ℕ} (hr : IsLetter r) :
    pkMat (selL (invL 19 2) (invL 99 19) (invL 114 2) (invL 115 19) r) = 𝕄 ((R5 r)⁻¹) := by
  rcases hr with rfl | rfl | rfl | rfl
  · rw [selL_19, mat_letter_inv (Or.inl rfl) inv_19]
  · rw [selL_99, mat_letter_inv (Or.inr (Or.inl rfl)) inv_99]
  · rw [selL_114, mat_letter_inv (Or.inr (Or.inr (Or.inl rfl))) inv_114]
  · rw [selL_115, mat_letter_inv (Or.inr (Or.inr (Or.inr rfl))) inv_115]

theorem prod_mat {X : ℕ → J} {H : ℕ → ℕ} (hH : ∀ r, IsLetter r → pkMat (H r) = 𝕄 (X r))
    {w : List ℕ} (hw : ∀ r ∈ w, IsLetter r) :
    (w.map fun r => pkMat (H r)).prod = 𝕄 ((w.map X).prod) := by
  rw [mat_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun r hr => hH r (hw r hr)

noncomputable def uElt (k : Fin 100) : J := ((P.U[k.val]'(by rw [len_ok]; exact k.2)).map R5).prod

theorem uElt_words (k : Fin 100) : ∀ r ∈ P.U[k.val]'(by rw [len_ok]; exact k.2), IsLetter r :=
  letsOK_sound P.U lets_ok _ (List.getElem_mem _)

theorem conjRow_eq (k : Fin 100) :
    pkVec (conjRow ThS.rm (selL (V5 19) (V5 99) (V5 114) (V5 115))
        (selL (invL 19 2) (invL 99 19) (invL 114 2) (invL 115 19)) (V5 19)
        (P.U[k.val]'(by rw [len_ok]; exact k.2))) =
      Matrix.vecMul (pkVec 1) (𝕄 (uElt k * R5 19 * (uElt k)⁻¹)) := by
  obtain ⟨-, -, -, hk⟩ := CertificateChecks.KernelThCent.fwd_mats
  have hw := uElt_words k
  have hwr : ∀ r ∈ (P.U[k.val]'(by rw [len_ok]; exact k.2)).reverse, IsLetter r :=
    fun r hr => hw r (List.mem_reverse.1 hr)
  have hinv : (uElt k)⁻¹ =
      ((P.U[k.val]'(by rw [len_ok]; exact k.2)).reverse.map fun r => (R5 r)⁻¹).prod := by
    rw [uElt, List.prod_inv_reverse, List.map_map, ← List.map_reverse]
    try rfl
  rw [pkVec_conjRow hk, prod_mat (fun r hr => selL_letter hr) hw,
    prod_mat (X := fun r => (R5 r)⁻¹) (fun r hr => selL_letter_inv hr) hwr, ← hinv,
    ← mat_letter (Or.inl rfl), mat_mul, mat_mul]
  try rfl

theorem thPump_kernel {t : J} (ht3 : orderOf t = 3) (htc : t * c5 = c5 * t) :
    Nat.card ↥(Subgroup.centralizer ({c5} : Set J) ⊓ Subgroup.centralizer ({t} : Set J)) ≤ 30 := by
  have : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  obtain ⟨-, -, -, hk⟩ := CertificateChecks.KernelThCent.fwd_mats
  have hmemL : ∀ w : List ℕ, (∀ r ∈ w, IsLetter r) →
      (w.map R5).prod ∈ Subgroup.centralizer ({c5} : Set J) := fun w hw =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (letter_comm (hw r hr))
  have ht₀C : R5 19 ∈ Subgroup.centralizer ({c5} : Set J) :=
    Subgroup.mem_centralizer_singleton_iff.2 (letter_comm (Or.inl rfl))
  have hc3 : powB ThS.c ThS.rm ThS.ONE (V5 19) 3 5 = ThS.ONE := Nat.eq_of_beq_eq_true cube_19
  have hcube : R5 19 ^ 3 = 1 := mat_inj (by
    rw [mat_pow, mat_letter (Or.inl rfl), ← pkMat_powB hk _ _ 5 (by norm_num), hc3,
      pkMat_one hk, mat_one])
  have hne : R5 19 ≠ 1 := fun e =>
    neB_sound hk ne_19 (by rw [← mat_letter (Or.inl rfl), e, mat_one, pkMat_one hk])
  have ht₀ : orderOf (R5 19) = 3 := orderOf_eq_prime hcube hne
  have hrows := rowsOK_sound _ _ _ _ P.U P.D (by
    have h := rows_ok
    simp only [strictF_eq] at h
    exact h)
  have hnd : (P.U.map (conjRow ThS.rm (selL (V5 19) (V5 99) (V5 114) (V5 115))
      (selL (invL 19 2) (invL 99 19) (invL 114 2) (invL 115 19)) (V5 19))).Nodup := by
    rw [← hrows]
    exact distinctL_sound _ dist_ok
  have hinj : ∀ k l : Fin 100, uElt k * R5 19 * (uElt k)⁻¹ = uElt l * R5 19 * (uElt l)⁻¹ →
      k = l := by
    intro k l e
    have e1 := conjRow_eq k
    have e2 := conjRow_eq l
    rw [e] at e1
    have e3 := pkVec_inj (conjRow_lt hk _ _ _ _) (conjRow_lt hk _ _ _ _) (e1.trans e2.symm)
    have hk' : k.val < (P.U.map (conjRow ThS.rm (selL (V5 19) (V5 99) (V5 114) (V5 115))
        (selL (invL 19 2) (invL 99 19) (invL 114 2) (invL 115 19)) (V5 19))).length := by
      rw [List.length_map, len_ok]
      exact k.2
    have hl' : l.val < (P.U.map (conjRow ThS.rm (selL (V5 19) (V5 99) (V5 114) (V5 115))
        (selL (invL 19 2) (invL 99 19) (invL 114 2) (invL 115 19)) (V5 19))).length := by
      rw [List.length_map, len_ok]
      exact l.2
    have := (List.Nodup.getElem_inj_iff hnd (hi := hk') (hj := hl')).1 (by
      rw [List.getElem_map, List.getElem_map]
      exact e3)
    exact Fin.ext this
  exact card_inf_centralizer_le_of_orbit ht₀C ht₀
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive.thFive_complete.2 uElt
    (fun k => hmemL _ (uElt_words k)) hinj (Subgroup.mem_centralizer_singleton_iff.2 htc) ht3

end CertificateChecks.KernelThPump

end
