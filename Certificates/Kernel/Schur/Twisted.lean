module

public import CFSG.Monster.Schur.CentralEps
public import CFSG.Monster.Schur.M24.Twist
public import Certificates.Kernel.Schur.Central
public import Certificates.Kernel.Schur.Ident
public import Certificates.Kernel.Schur.TablesC
public import Certificates.Kernel.Schur.CoverIds
public import Certificates.Kernel.M23Mult.Bounds

public section

namespace CertificateChecks.KernelSchur

open CFSG.Certificates CFSG.Certificates.KB CFSG.KC CFSG.KC.MiscCoset CFSG.Monster.Schur
  CFSG.Monster.Schur.M24 CFSG.CosetTable CFSG.Sporadic.Recognition.M23Multiplier
  CFSG.LieType.Multipliers CFSG.KC.Schur.Id CFSG.KC.Schur.Words
open scoped commutatorElement

section Cover

variable {G : Type*} [Group G] {z : G} (hz : ∀ g, z * g = g * z) (hz2 : z * z = 1)
include hz hz2

omit hz2 in
theorem sign_cen {s : G} (hs : IsSign z s) : Cen s := fun g => sign_comm hz hs g

theorem cover_bound (h : Fin 6 → G)
    (hR : ∀ w ∈ m23Rels, IsSign z (FreeGroup.lift h (FreeGroup.mk w)))
    (hW : ∀ i, IsSign z ((h i)⁻¹ * FreeGroup.lift h (FreeGroup.mk (m23CommWord i)))) :
    ∃ S : Subgroup G, Finite S ∧ Nat.card S ≤ 10200960 ∧ ∀ i, h i ∈ S ⊔ Subgroup.zpowers z := by
  set g : Fin 6 → G := fun i => FreeGroup.lift h (FreeGroup.mk (m23CommWord i)) with hgdef
  set c : Fin 6 → G := fun i => (h i)⁻¹ * g i with hcdef
  have hc : ∀ i, Cen (c i) := fun i => sign_cen hz (hW i)
  have hg : ∀ i, g i = h i * c i := fun i => by simp [hcdef]
  have hrel : ∀ r ∈ coverRelators (wordSet m23Rels) m23CommW, FreeGroup.lift g r = 1 := by
    rintro x (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      obtain ⟨k, hk, e⟩ := lift_central hc hg (FreeGroup.mk w)
      have hcen : Cen (FreeGroup.lift g (FreeGroup.mk w)) := by
        rw [e]
        exact cen_mul (sign_cen hz (hR w hw)) hk
      rw [map_commutatorElement, FreeGroup.lift_apply_of, commutatorElement_def, ← hcen (g i)]
      group
    · have e : FreeGroup.lift g (m23CommW i) = g i :=
        lift_commWords_central hc hg (m23Comm i)
      rw [map_mul, map_inv, FreeGroup.lift_apply_of, e, inv_mul_cancel]
  have hfin := CertificateChecks.KernelM23Mult.card_cover.1
  have hcard := CertificateChecks.KernelM23Mult.card_cover.2
  set φ : M23Cover →* G := PresentedGroup.toGroup hrel with hφ
  refine ⟨φ.range, Finite.of_surjective _ φ.rangeRestrict_surjective,
    (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans hcard, fun i => ?_⟩
  have hgi : g i ∈ φ.range := ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  have hci : (c i)⁻¹ ∈ Subgroup.zpowers z :=
    Subgroup.inv_mem _ ((mem_zpowers_iff_sign hz2).2 (hW i))
  have e : h i = g i * (c i)⁻¹ := by simp [hcdef]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgi) (Subgroup.mem_sup_right hci)

end Cover

theorem crels_sub : ∀ c0 c1 c2 c3 c4 : Bool, ∀ r ∈ CFSG.KC.SchurC.crels c0 c1 c2 c3 c4,
    r = [(2, true), (0, true), (2, false), (0, false)] ∨
      r = [(2, true), (1, true), (2, false), (1, false)] ∨
      r ∈ (epsRels U T5 ![c0, c1, c2, c3, c4]).map encW := by
  decide +kernel

theorem m24rels_eq : CFSG.KBAlt.M24.rels = [encW (castWord (T5 0)), encW (castWord b3),
    encW (castWord ab23), encW (castWord (T5 1)), encW (castWord (T5 2)),
    encW (castWord (T5 3)), encW (castWord (T5 4))] := by
  decide +kernel

theorem coverW_eq : (List.finRange 6).map (fun i => encW ((i, false) :: m23CommWord i)) =
    CertificateChecks.KernelM23Mult.coverW := by
  decide +kernel

theorem substK_eq (ims : List (List (ℕ × Bool))) (w : List (ℕ × Bool)) :
    substK ims w = subst (fun n => ims.getD n []) w := rfl

theorem winvK_eq (w : List (ℕ × Bool)) : winvK w = winv w := rfl

theorem encW_append {m : ℕ} (u v : List (Fin m × Bool)) : encW (u ++ v) = encW u ++ encW v := by
  simp [encW]

section Gamma

variable (e : Fin 5 → Bool)

noncomputable abbrev yy : ℕ → PG (2 + 1) (epsRels U T5 e) := pgGen (epsRels U T5 e)

theorem rel_one {w : List (Fin (2 + 1) × Bool)} (hw : w ∈ epsRels U T5 e) :
    sword (yy e) (encW w) = 1 :=
  sword_rels (epsRels U T5 e) rfl _ (List.mem_map_of_mem hw)

theorem z_sq : yy e 2 * yy e 2 = 1 := by
  have h := rel_one e (w := [zLetter 2, zLetter 2]) (by simp [epsRels])
  simpa [sword, encW, zLetter] using h

theorem z_comm_gen (i : Fin 2) : yy e 2 * yy e i.val = yy e i.val * yy e 2 := by
  have h := rel_one e (w := [zLetter 2, (i.castSucc, true), zLetter 2, (i.castSucc, false)])
    (by simp [epsRels])
  have h' : yy e 2 * yy e i.val * yy e 2 * (yy e i.val)⁻¹ = 1 := by
    simpa [sword, encW, zLetter, mul_assoc] using h
  have hzi : (yy e 2)⁻¹ = yy e 2 := inv_eq_of_mul_eq_one_right (z_sq e)
  calc yy e 2 * yy e i.val = yy e 2 * yy e i.val * yy e 2 * (yy e i.val)⁻¹ *
        (yy e i.val * (yy e 2)⁻¹) := by group
    _ = yy e i.val * yy e 2 := by rw [h', one_mul, hzi]

theorem z_central : ∀ g, yy e 2 * g = g * yy e 2 := by
  have htop : Subgroup.closure (yy e '' {g | g < 2 + 1}) ≤
      Subgroup.centralizer {yy e 2} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    simp only [Set.mem_ofPred_eq] at hn
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
    · exact z_comm_gen e 0
    · exact z_comm_gen e 1
    · rfl
  rw [closure_pgGen] at htop
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top g)) _ rfl)

theorem sign_T5 (i : Fin 5) : IsSign (yy e 2) (sword (yy e) (encW (castWord (T5 i)))) := by
  have h := rel_one e (w := castWord (T5 i) ++ (if e i then [zLetter 2] else []))
    (by simp [epsRels])
  rw [encW_append, sword_append] at h
  have hzi : (yy e 2)⁻¹ = yy e 2 := inv_eq_of_mul_eq_one_right (z_sq e)
  cases he : e i <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at h
  · left
    simpa [encW, sword] using h
  · right
    have h' : sword (yy e) (encW (castWord (T5 i))) * yy e 2 = 1 := by
      simpa [encW, sword, zLetter] using h
    rw [eq_inv_of_mul_eq_one_left h', hzi]

theorem sign_U {u : List (Fin 2 × Bool)} (hu : u ∈ U) :
    sword (yy e) (encW (castWord u)) = 1 :=
  rel_one e (List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hu))))

theorem sign_m24 : ∀ w ∈ CFSG.KBAlt.M24.rels, IsSign (yy e 2) (sword (yy e) w) := by
  rw [m24rels_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact sign_T5 e 0
  · exact Or.inl (sign_U e (by simp [U]))
  · exact Or.inl (sign_U e (by simp [U]))
  · exact sign_T5 e 1
  · exact sign_T5 e 2
  · exact sign_T5 e 3
  · exact sign_T5 e 4

theorem ident {w : List (ℕ × Bool)} (h : idOK w = true) : IsSign (yy e 2) (sword (yy e) w) := by
  have hz := z_central e
  have hz2 := z_sq e
  have : (Subgroup.zpowers (yy e 2)).Normal := zpowers_normal hz
  set q := QuotientGroup.mk' (Subgroup.zpowers (yy e 2))
  simp only [idOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  have hy : ∀ r ∈ CFSG.KBAlt.M24.rels, sword (fun i => q (yy e i)) r = 1 := by
    intro r hr
    rw [sword_map, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_iff_sign hz2]
    exact sign_m24 e r hr
  have h1 := m24_reads (fun i => q (yy e i)) hy w h.1 rfl h.2
  rw [sword_map, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zpowers_iff_sign hz2]
    at h1
  exact h1

noncomputable abbrev zf (n : ℕ) : PG (2 + 1) (epsRels U T5 e) := sword (yy e) (us.getD n [])

theorem lift_zf (w : List (Fin 6 × Bool)) :
    FreeGroup.lift (fun i : Fin 6 => zf e i.val) (FreeGroup.mk w) =
      sword (yy e) (substK us (encW w)) := by
  rw [lift_mk_eq_sword, substK_eq, sword_subst]
  rfl

theorem bound_core (hne : ∃ i, e i = true)
    (hc : ∀ r ∈ CFSG.KC.SchurC.crels (e 0) (e 1) (e 2) (e 3) (e 4), sword (yy e) r = 1)
    (hne' : e 0 = true ∨ e 1 = true ∨ e 2 = true ∨ e 3 = true ∨ e 4 = true) :
    Finite (PG (2 + 1) (epsRels U T5 e)) ∧ Nat.card (PG (2 + 1) (epsRels U T5 e)) ≤ 244823040 := by
  have hz := z_central e
  have hz2 := z_sq e
  have hR : ∀ w ∈ m23Rels, IsSign (yy e 2)
      (FreeGroup.lift (fun i : Fin 6 => zf e i.val) (FreeGroup.mk w)) := by
    intro w hw
    rw [lift_zf]
    apply ident
    have hm : encW w ∈ CertificateChecks.KernelM23Mult.rels6 := by
      rw [← CertificateChecks.KernelM23Mult.rels6_eq]
      exact List.mem_map_of_mem hw
    exact List.all_eq_true.1 CoverIds.rels _ hm
  have hW : ∀ i : Fin 6, IsSign (yy e 2) ((zf e i.val)⁻¹ *
      FreeGroup.lift (fun i : Fin 6 => zf e i.val) (FreeGroup.mk (m23CommWord i))) := by
    intro i
    have hm : encW ((i, false) :: m23CommWord i) ∈ CertificateChecks.KernelM23Mult.coverW := by
      rw [← coverW_eq]
      exact List.mem_map_of_mem (List.mem_finRange i)
    have h := ident e (List.all_eq_true.1 CoverIds.cover _ hm)
    rw [← lift_zf] at h
    have e1 : FreeGroup.mk ((i, false) :: m23CommWord i) =
        (FreeGroup.of i)⁻¹ * FreeGroup.mk (m23CommWord i) := rfl
    rwa [e1, map_mul, map_inv, FreeGroup.lift_apply_of] at h
  obtain ⟨S, hSfin, hScard, hSmem⟩ := cover_bound hz hz2 _ hR hW
  have hcl : Subgroup.closure (zf e '' {n | n < 6}) ≤ S ⊔ Subgroup.zpowers (yy e 2) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact hSmem ⟨n, hn⟩
  have hodd : wordSub (yy e) oddWords ≤ S := by
    rw [wordSub, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_ofPred_eq, oddWords, List.mem_map] at hw
    obtain ⟨o, ho, rfl⟩ := hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
    have hk5 : k < 5 := hk
    rw [SetLike.mem_coe, sword_replicate]
    set u := sword (yy e) odds[k]
    have hv : ∀ x ∈ vs.getD k [], x.1 < 6 := by
      interval_cases k <;> decide +kernel
    have h1 := ident e (List.all_eq_true.1 CoverIds.odd k (List.mem_range.2 hk5))
    rw [sword_append, winvK_eq, sword_winv, substK_eq, sword_subst,
      List.getD_eq_getElem _ _ hk] at h1
    have hX := sword_mem_closure (zf e) (vs.getD k []) hv
    have hu : u ∈ S ⊔ Subgroup.zpowers (yy e 2) := by
      have e2 : u = u * (sword (zf e) (vs.getD k []))⁻¹ * sword (zf e) (vs.getD k []) := by
        group
      rw [e2]
      refine Subgroup.mul_mem _ ?_ (hcl hX)
      exact Subgroup.mem_sup_right ((mem_zpowers_iff_sign hz2).2 h1)
    have h3 := ident e (List.all_eq_true.1 CoverIds.cubes _ (List.getElem_mem hk))
    rw [sword_replicate] at h3
    have h3' : IsSign (yy e 2) (u ^ 3) := h3
    apply mem_of_cube hz hz2 (Subgroup.pow_mem _ hu 4)
    rw [← pow_mul, show 4 * 3 = 3 * 4 by rfl, pow_mul]
    rcases h3' with h | h <;> rw [h]
    · exact one_pow 4
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hz2, one_mul]
  obtain ⟨-, b2, b3⟩ := bound_c (yy e) _ _ _ _ _ hne' hc
  have htop : Subgroup.closure (yy e '' {g | g < 3}) = ⊤ := closure_pgGen _
  rw [htop, Subgroup.relIndex_top_right] at b2 b3
  have hle := Subgroup.card_le_of_le hodd
  have hmul := (wordSub (yy e) oddWords).index_mul_card
  have hWfin : Finite (wordSub (yy e) oddWords) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hodd)
  have hpos : 0 < Nat.card (wordSub (yy e) oddWords) := Nat.card_pos
  have hcardE : Nat.card (PG (2 + 1) (epsRels U T5 e)) ≤ 24 * 10200960 := by
    rw [← hmul]
    exact Nat.mul_le_mul b3 (hle.trans hScard)
  refine ⟨Nat.finite_of_card_ne_zero ?_, hcardE.trans (by norm_num)⟩
  rw [← hmul]
  exact Nat.mul_ne_zero b2 hpos.ne'

end Gamma

theorem bound_twisted (c0 c1 c2 c3 c4 : Bool)
    (hne : c0 = true ∨ c1 = true ∨ c2 = true ∨ c3 = true ∨ c4 = true) :
    Finite (PG (2 + 1) (epsRels U T5 ![c0, c1, c2, c3, c4])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![c0, c1, c2, c3, c4])) ≤ 244823040 := by
  set e : Fin 5 → Bool := ![c0, c1, c2, c3, c4]
  have hz := z_central e
  have hz2 := z_sq e
  have hzi : (yy e 2)⁻¹ = yy e 2 := inv_eq_of_mul_eq_one_right hz2
  have hc : ∀ r ∈ CFSG.KC.SchurC.crels (e 0) (e 1) (e 2) (e 3) (e 4), sword (yy e) r = 1 := by
    intro r hr
    rcases crels_sub c0 c1 c2 c3 c4 r hr with rfl | rfl | h
    · simp only [sword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ↓reduceIte, Bool.false_eq_true]
      rw [← mul_assoc, ← mul_assoc, hz, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    · simp only [sword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        ↓reduceIte, Bool.false_eq_true]
      rw [← mul_assoc, ← mul_assoc, hz, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact rel_one e hw
  have hne' : ∃ i, e i = true := by
    rcases hne with h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  exact bound_core e hne' hc hne

end CertificateChecks.KernelSchur

end
