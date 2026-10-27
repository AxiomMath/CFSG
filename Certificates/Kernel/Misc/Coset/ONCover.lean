module

public import CFSG.RankThree.Native.ONTripleModel
public import Certificates.Kernel.Misc.Coset.XONU
public import Certificates.Kernel.Misc.Coset.C8144

public section

namespace CertificateChecks.KernelMiscCoset.ONCover

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.RankThree.Native.ONTriple CFSG.Certificates
open scoped Pointwise

@[expose] def liftL (w : List (Fin 8 × Bool)) : List (Fin 10 × Bool) :=
  w.map fun l => (Fin.castLE (by norm_num) l.1, l.2)

@[expose] def commW (c x : Fin 10) : List (Fin 10 × Bool) :=
  [(c, true), (x, true), (c, false), (x, false)]

@[expose] def Urels : List (List (Fin 10 × Bool)) :=
  ((coverRels 0 0 0).take 26).map liftL ++
    [liftL ((coverRels 0 0 0).getD 26 []) ++ [(7, false)],
      liftL ((coverRels 0 0 0).getD 27 []) ++ [(8, false)],
      liftL ((coverRels 0 0 0).getD 28 []) ++ [(9, false)],
      [(7, true), (7, true), (7, true)], [(8, true), (8, true), (8, true)],
      [(9, true), (9, true), (9, true)]] ++
    ([7, 8, 9] : List (Fin 10)).flatMap fun c =>
      (List.finRange 7).map fun x => commW c (Fin.castLE (by norm_num) x)

abbrev U : Type := PG 10 Urels

abbrev Urel : Set (FreeGroup (Fin 10)) := {r : FreeGroup (Fin 10) | r ∈ Urels.map FreeGroup.mk}

noncomputable abbrev gU (i : Fin 10) : U := PresentedGroup.of i

theorem rU : Urels.map encW = CFSG.KBRoute.XONU.rels := by decide +kernel

theorem wU : CFSG.KBRoute.XONU.T1.words =
    (subsetOf 10 [0, 1, 2, 3, 4, 5, 7]).map fun x => [(x.val, true)] := by decide +kernel

theorem mk_eq_prod (w : List (Fin 10 × Bool)) :
    (PresentedGroup.mk Urel (FreeGroup.mk w) : U) =
      (w.map fun l => if l.2 then gU l.1 else (gU l.1)⁻¹).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul, ih,
      List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨j, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      rfl
    · rfl

theorem prod_one_of_mem {w : List (Fin 10 × Bool)} (hw : w ∈ Urels) :
    (w.map fun l => if l.2 then gU l.1 else (gU l.1)⁻¹).prod = 1 := by
  rw [← mk_eq_prod]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem commW_mem (x : Fin 7) : commW 7 (Fin.castLE (by norm_num) x) ∈ Urels := by
  simp only [Urels, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨7, by decide, x, List.mem_finRange x, rfl⟩

theorem commute_u (x : Fin 7) : Commute (gU 7) (gU (Fin.castLE (by norm_num) x)) := by
  have h := prod_one_of_mem (commW_mem x)
  simp only [commW, List.map_cons, List.map_nil, ↓reduceIte, Bool.false_eq_true,
    List.prod_cons, List.prod_nil, mul_one] at h
  rw [← mul_assoc, ← mul_assoc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem u_cube : gU 7 ^ 3 = 1 := by
  have h := prod_one_of_mem (w := [(7, true), (7, true), (7, true)]) (by
    simp only [Urels, List.mem_append, List.mem_cons]
    decide)
  simpa [pow_succ, mul_assoc] using h

theorem restrict6 :
    (restrictWords (subsetOf 10 [0, 1, 2, 3, 4, 5]) Urels).map encW = C1.map encW := by
  decide +kernel

theorem encW_injective {m : ℕ} :
    Function.Injective (encW : List (Fin m × Bool) → List (ℕ × Bool)) :=
  List.map_injective_iff.2 fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) h.2

theorem card_PG_congr {m n : ℕ} (h : m = n) {ws : List (List (Fin m × Bool))}
    {vs : List (List (Fin n × Bool))} (hw : ws.map encW = vs.map encW) (hf : Finite (PG n vs)) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) = Nat.card (PG n vs) := by
  subst h
  obtain rfl : ws = vs := List.map_injective_iff.2 encW_injective hw
  exact ⟨hf, rfl⟩

noncomputable abbrev A : Subgroup U := genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5])

theorem card_A : Finite A ∧ Nat.card A ≤ 3753792 := by
  obtain ⟨hf, hc⟩ := C8144.card_coxeter_le
  obtain ⟨hf', hc'⟩ := card_PG_congr (by rfl) restrict6 hf
  obtain ⟨h1, h2⟩ := card_genSub_le Urels (subsetOf 10 [0, 1, 2, 3, 4, 5])
  exact ⟨h1, h2.trans (hc' ▸ hc)⟩

noncomputable abbrev N : Subgroup U := Subgroup.zpowers (gU 7)

theorem card_N : Finite N ∧ Nat.card N ≤ 3 := by
  have hd : orderOf (gU 7) ∣ 3 := orderOf_dvd_of_pow_eq_one u_cube
  have hpos : 0 < orderOf (gU 7) := Nat.pos_of_dvd_of_pos hd (by norm_num)
  refine ⟨Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega), ?_⟩
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) hd

theorem A_le_normalizer : A ≤ Subgroup.normalizer (N : Set U) := by
  refine le_trans ((Subgroup.closure_le _).2 ?_) (Subgroup.centralizer_le_normalizer _)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ subsetOf 10 [0, 1, 2, 3, 4, 5] := hx
  have hx6 : x.val < 6 := by
    clear hx
    revert x
    decide +kernel
  have hc : Commute (gU 7) (PresentedGroup.of x) := commute_u ⟨x.val, by omega⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  exact (hc.zpow_left k).eq

theorem genSub7_le : genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5, 7]) ≤ A ⊔ N := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ subsetOf 10 [0, 1, 2, 3, 4, 5, 7] := hx
  have : x ∈ subsetOf 10 [0, 1, 2, 3, 4, 5] ∨ x = 7 := by
    clear hx
    revert x
    decide +kernel
  rcases this with h | rfl
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, h, rfl⟩)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem card_genSub7 : Finite (genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5, 7])) ∧
    Nat.card (genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5, 7])) ≤ 3753792 * 3 := by
  obtain ⟨hAf, hAc⟩ := card_A
  obtain ⟨hNf, hNc⟩ := card_N
  have hset : ((A ⊔ N : Subgroup U) : Set U) = (A : Set U) * (N : Set U) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A N A_le_normalizer
  have hfin : Finite (A ⊔ N : Subgroup U) := by
    have : ((A : Set U) * (N : Set U)).Finite :=
      (Set.finite_coe_iff.1 hAf).mul (Set.finite_coe_iff.1 hNf)
    rw [← hset] at this
    exact this.to_subtype
  have hc : Nat.card (A ⊔ N : Subgroup U) ≤ 3753792 * 3 := by
    have := Set.natCard_mul_le (s := (A : Set U)) (t := (N : Set U))
    rw [← hset] at this
    exact this.trans (Nat.mul_le_mul hAc hNc)
  exact ⟨Finite.of_injective _ (Subgroup.inclusion_injective genSub7_le),
    (Subgroup.card_le_of_le genSub7_le).trans hc⟩

theorem card_U_le : Finite U ∧ Nat.card U ≤ 1382446517760 := by
  have h := XONU.t1
  unfold CFSG.KBRoute.XONU.T1.ok at h
  obtain ⟨hi, hidx⟩ :=
    genSub_index_le_of_tableOk Urels rU h (by decide) CFSG.KBRoute.XONU.top _ wU
  obtain ⟨hf, hc⟩ := card_genSub7
  have hU : Finite U := by
    have : Finite (U ⧸ genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5, 7])) :=
      Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5, 7]))
  refine ⟨hU, ?_⟩
  rw [← (genSub Urel (subsetOf 10 [0, 1, 2, 3, 4, 5, 7])).index_mul_card]
  exact (Nat.mul_le_mul hidx hc).trans (by norm_num)

@[expose] def sigma (i : Fin 10) : Fin 8 := if h : i.val < 7 then ⟨i.val, by omega⟩ else 7

theorem map_sigma_mem : ∀ w ∈ Urels, w.map (fun l => (sigma l.1, l.2)) ∈ coverRels 1 1 1 := by
  decide +kernel

theorem lift_of_mk {n : ℕ} (rels : Set (FreeGroup (Fin n))) (σ : Fin 10 → Fin n)
    (w : List (Fin 10 × Bool)) :
    FreeGroup.lift (fun i => (PresentedGroup.of (σ i) : PresentedGroup rels)) (FreeGroup.mk w) =
      PresentedGroup.mk rels (FreeGroup.mk (w.map fun l => (σ l.1, l.2))) := by
  have : FreeGroup.lift (fun i => (PresentedGroup.of (σ i) : PresentedGroup rels)) =
      (PresentedGroup.mk rels).comp (FreeGroup.map σ) :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
      rfl
  rw [this, MonoidHom.comp_apply, FreeGroup.map.mk]

noncomputable def phi : U →* FHat 1 1 1 :=
  PresentedGroup.toGroup (f := fun i => (PresentedGroup.of (sigma i) : FHat 1 1 1)) (by
    intro r hr
    have hr' : r ∈ Urels.map FreeGroup.mk := hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr'
    rw [lift_of_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (map_sigma_mem w hw)))

theorem phi_of (i : Fin 10) : phi (gU i) = PresentedGroup.of (sigma i) :=
  PresentedGroup.toGroup.of _

theorem piphi_surjective : Function.Surjective (piON.comp phi) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hi : i.val < 7 := by
    have h1 := i.isLt
    have h2 := generatorCount_PON
    omega
  refine ⟨gU ⟨i.val, by omega⟩, ?_⟩
  rw [MonoidHom.comp_apply, phi_of]
  have : sigma ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := by simp [sigma, hi]
  rw [this, piON_of]
  exact pGen_of PON i

noncomputable abbrev K : Subgroup U := (piON.comp phi).ker

theorem card_K : Nat.card K ≤ 3 := by
  have hk : Nat.card K * Nat.card PON.Group = Nat.card U :=
    Subgroup.card_ker_mul_card_of_surjective piphi_surjective
  rw [card_PON] at hk
  have := card_U_le.2
  omega

theorem mem_K {j : Fin 10} (hj : sigma j = 7) : gU j ∈ K := by
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, phi_of, hj]
  exact MonoidHom.mem_ker.1 zF_mem_ker

theorem phi_eq_zF {j : Fin 10} (hj : sigma j = 7) : phi (gU j) = zF := by
  rw [phi_of, hj]
  rfl

theorem orderOf_u : orderOf (gU 7) = 3 := by
  have h1 : orderOf (gU 7) ∣ 3 := orderOf_dvd_of_pow_eq_one u_cube
  have h2 : orderOf (phi (gU 7)) ∣ orderOf (gU 7) := orderOf_map_dvd phi _
  rw [phi_eq_zF rfl, orderOf_zF] at h2
  exact Nat.dvd_antisymm h1 h2

theorem K_eq : N = K := by
  have := card_U_le.1
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact mem_K rfl
  · rw [Nat.card_zpowers, orderOf_u]
    exact card_K

theorem gU_seven_eq {j : Fin 10} (hj : sigma j = 7) : gU 7 = gU j := by
  have hv : gU j ∈ N := by
    rw [K_eq]
    exact mem_K hj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
  have h1 : zF ^ k = zF := by
    have := congrArg phi hk
    rwa [map_zpow, phi_eq_zF rfl, phi_eq_zF hj] at this
  have h2 : ((orderOf zF : ℕ) : ℤ) ∣ k - 1 :=
    orderOf_dvd_iff_zpow_eq_one.2 (by rw [zpow_sub_one, h1, mul_inv_cancel])
  rw [orderOf_zF, ← orderOf_u] at h2
  have h3 := orderOf_dvd_iff_zpow_eq_one.1 h2
  rw [zpow_sub_one, mul_inv_eq_one, hk] at h3
  exact h3.symm

section Psi

variable (e₁ e₂ e₃ : ℕ)

@[expose] noncomputable def psiImg (i : Fin 10) : FHat e₁ e₂ e₃ :=
  if h : i.val < 7 then PresentedGroup.of ⟨i.val, by omega⟩
  else if i.val = 7 then C8144.zz e₁ e₂ e₃ ^ e₁
  else if i.val = 8 then C8144.zz e₁ e₂ e₃ ^ e₂ else C8144.zz e₁ e₂ e₃ ^ e₃

variable {e₁ e₂ e₃}

theorem take26 : (coverRels e₁ e₂ e₃).take 26 = (coverRels 0 0 0).take 26 := rfl

theorem take26_lt : ∀ v ∈ (coverRels 0 0 0).take 26, ∀ l ∈ v, l.1.val < 7 := by decide +kernel

theorem mk_cons {n : ℕ} (rels : Set (FreeGroup (Fin n))) (l : Fin n × Bool)
    (v : List (Fin n × Bool)) :
    PresentedGroup.mk rels (FreeGroup.mk (l :: v)) =
      (if l.2 then PresentedGroup.of l.1 else (PresentedGroup.of l.1)⁻¹) *
        PresentedGroup.mk rels (FreeGroup.mk v) := by
  rw [show FreeGroup.mk (l :: v) = FreeGroup.mk [l] * FreeGroup.mk v from rfl, map_mul]
  congr 1
  obtain ⟨j, b⟩ := l
  cases b
  · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
    rfl
  · rfl

theorem prod_liftL (v : List (Fin 8 × Bool)) (hv : ∀ l ∈ v, l.1.val < 7) :
    ((liftL v).map fun l => cond l.2 (psiImg e₁ e₂ e₃ l.1) (psiImg e₁ e₂ e₃ l.1)⁻¹).prod =
      PresentedGroup.mk _ (FreeGroup.mk v) := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [liftL, List.map_cons, List.map_cons, List.prod_cons, ← liftL,
      ih fun l' hl' => hv l' (List.mem_cons_of_mem _ hl'), mk_cons]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj : j.val < 7 := hv _ List.mem_cons_self
    have : psiImg e₁ e₂ e₃ (Fin.castLE (by norm_num) j) = PresentedGroup.of j := by
      simp only [psiImg, Fin.val_castLE, hj, ↓reduceDIte]
    cases b <;> simp [this]

theorem mk_zInv (k : ℕ) :
    PresentedGroup.mk _ (FreeGroup.mk (zInv k)) = (C8144.zz e₁ e₂ e₃)⁻¹ ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [zInv, List.replicate_succ, mk_cons, ← zInv, ih, pow_succ']
    rfl

theorem mem_getD {i : ℕ} (hi : i < 37) : (coverRels e₁ e₂ e₃).getD i [] ∈ coverRels e₁ e₂ e₃ := by
  have hl : i < (coverRels e₁ e₂ e₃).length := by simpa [coverRels] using hi
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem hl

theorem mk_getD_one {i : ℕ} (hi : i < 37) :
    (PresentedGroup.mk _ (FreeGroup.mk ((coverRels e₁ e₂ e₃).getD i [])) : FHat e₁ e₂ e₃) = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_getD hi))

theorem zz_pow_cube (k : ℕ) : (C8144.zz e₁ e₂ e₃ ^ k) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, C8144.z_pow_three, one_pow]

theorem zz_pow_center (k : ℕ) :
    C8144.zz e₁ e₂ e₃ ^ k ∈ Subgroup.center (PG 8 (coverRels e₁ e₂ e₃)) :=
  Subgroup.pow_mem _ C8144.z_mem_center k

theorem prod_commW {G : Type*} [Group G] (f : Fin 10 → G) (c x : Fin 10)
    (h : f c ∈ Subgroup.center G) :
    ((commW c x).map fun l => cond l.2 (f l.1) (f l.1)⁻¹).prod = 1 := by
  rw [Subgroup.mem_center_iff] at h
  simp only [commW, List.map_cons, List.map_nil, cond_true, cond_false, List.prod_cons,
    List.prod_nil, mul_one]
  rw [← mul_assoc, ← h (f x), mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

theorem prod_tail (r : List (Fin 8 × Bool)) (hr : ∀ l ∈ r, l.1.val < 7) (c : Fin 10) (k : ℕ)
    (hc : psiImg e₁ e₂ e₃ c = C8144.zz e₁ e₂ e₃ ^ k)
    (hrel : (PresentedGroup.mk _ (FreeGroup.mk (r ++ zInv k)) : FHat e₁ e₂ e₃) = 1) :
    ((liftL r ++ [(c, false)]).map fun l =>
      cond l.2 (psiImg e₁ e₂ e₃ l.1) (psiImg e₁ e₂ e₃ l.1)⁻¹).prod = 1 := by
  rw [List.map_append, List.prod_append, prod_liftL r hr]
  rw [← FreeGroup.mul_mk, map_mul, mk_zInv] at hrel
  simpa [hc, inv_pow] using hrel

theorem psi_rel : ∀ r ∈ Urel, FreeGroup.lift (psiImg e₁ e₂ e₃) r = 1 := by
  intro r hr
  have hr' : r ∈ Urels.map FreeGroup.mk := hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr'
  rw [FreeGroup.lift_mk]
  simp only [Urels, List.mem_append, List.mem_map, List.mem_cons, List.mem_flatMap,
    List.mem_nil_iff, or_false] at hw
  rcases hw with ((⟨v, hv, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨c, hc, x, -, rfl⟩)
  · rw [prod_liftL v (take26_lt v hv)]
    rw [← take26 (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)] at hv
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (List.mem_of_mem_take hv))
  · exact prod_tail _ (by decide +kernel) 7 e₁ (by simp [psiImg]) (mk_getD_one (i := 26) (by norm_num))
  · exact prod_tail _ (by decide +kernel) 8 e₂ (by simp [psiImg]) (mk_getD_one (i := 27) (by norm_num))
  · exact prod_tail _ (by decide +kernel) 9 e₃ (by simp [psiImg]) (mk_getD_one (i := 28) (by norm_num))
  · simpa [psiImg, pow_succ, mul_assoc] using zz_pow_cube (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) e₁
  · simpa [psiImg, pow_succ, mul_assoc] using zz_pow_cube (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) e₂
  · simpa [psiImg, pow_succ, mul_assoc] using zz_pow_cube (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) e₃
  · apply prod_commW
    try simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simpa [psiImg] using zz_pow_center (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) e₁
    · simpa [psiImg] using zz_pow_center (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) e₂
    · simpa [psiImg] using zz_pow_center (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) e₃

noncomputable def psi : U →* FHat e₁ e₂ e₃ := PresentedGroup.toGroup psi_rel

theorem psi_of (i : Fin 10) : psi (gU i) = psiImg e₁ e₂ e₃ i := PresentedGroup.toGroup.of _

theorem zz_pow_eq : C8144.zz e₁ e₂ e₃ ^ e₁ = C8144.zz e₁ e₂ e₃ ^ e₂ ∧
    C8144.zz e₁ e₂ e₃ ^ e₂ = C8144.zz e₁ e₂ e₃ ^ e₃ := by
  have h8 := congrArg (psi (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)) (gU_seven_eq (j := 8) rfl)
  have h9 := congrArg (psi (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)) (gU_seven_eq (j := 9) rfl)
  simp only [psi_of, psiImg] at h8 h9
  norm_num at h8 h9
  exact ⟨h8, h8.symm.trans h9⟩

theorem eq_one_of_pow_eq {G : Type*} [Group G] {z : G} (hz : z ^ 3 = 1) {a b : ℕ} (ha : a < 3)
    (hb : b < 3) (hab : a ≠ b) (h : z ^ a = z ^ b) : z = 1 := by
  have key : ∀ d, 0 < d → d < 3 → z ^ d = 1 → z = 1 := by
    intro d h0 h3 hd
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz
    have h2 : orderOf z ∣ d := orderOf_dvd_of_pow_eq_one hd
    have : orderOf z ∣ Nat.gcd 3 d := Nat.dvd_gcd h1 h2
    interval_cases d <;> simpa using this
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · refine key (b - a) (by omega) (by omega) ?_
    have e : z ^ a * z ^ (b - a) = z ^ a * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, h]
    exact mul_left_cancel e
  · refine key (a - b) (by omega) (by omega) ?_
    have e : z ^ b * z ^ (a - b) = z ^ b * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, h]
    exact mul_left_cancel e

theorem zz_eq_one (h₁ : e₁ < 3) (h₂ : e₂ < 3) (h₃ : e₃ < 3) (hne : ¬ (e₁ = e₂ ∧ e₂ = e₃)) :
    C8144.zz e₁ e₂ e₃ = 1 := by
  obtain ⟨h12, h23⟩ := zz_pow_eq (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
  by_cases h : e₁ = e₂
  · exact eq_one_of_pow_eq C8144.z_pow_three h₂ h₃ (fun h' => hne ⟨h, h'⟩) h23
  · exact eq_one_of_pow_eq C8144.z_pow_three h₁ h₂ h h12

end Psi

theorem on_rels_getD : ∀ r ∈ CFSG.KBRoute.ON.rels,
    ∃ i < 29, r = encW ((coverRels 0 0 0).getD i []) := by decide +kernel

theorem getD_eq {e₁ e₂ e₃ i : ℕ} (hi : i < 29) : ∃ k, (coverRels e₁ e₂ e₃).getD i [] =
    (coverRels 0 0 0).getD i [] ++ zInv k := by
  interval_cases i
  all_goals first
    | exact ⟨0, rfl⟩
    | exact ⟨e₁, rfl⟩
    | exact ⟨e₂, rfl⟩
    | exact ⟨e₃, rfl⟩

theorem card_FHat_le {e₁ e₂ e₃ : ℕ} (h₁ : e₁ < 3) (h₂ : e₂ < 3) (h₃ : e₃ < 3)
    (hne : ¬ (e₁ = e₂ ∧ e₂ = e₃)) :
    Finite (PG 8 (coverRels e₁ e₂ e₃)) ∧ Nat.card (PG 8 (coverRels e₁ e₂ e₃)) ≤ 460815505920 := by
  have hz := zz_eq_one h₁ h₂ h₃ hne
  set gen := pgGen (coverRels e₁ e₂ e₃)
  have hg7 : gen 7 = 1 := by
    have : gen 7 = C8144.zz e₁ e₂ e₃ := by
      simp only [gen, pgGen, show (7 : ℕ) < 8 from by norm_num, ↓reduceDIte]
      rfl
    rw [this, hz]
  have hzinv : ∀ k, KB.sword gen (encW (zInv k)) = 1 := by
    intro k
    simp [KB.sword, encW, zInv, hg7]
  have hrels : ∀ r ∈ CFSG.KBRoute.ON.rels, KB.sword gen r = 1 := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := on_rels_getD r hr
    obtain ⟨k, hk⟩ := getD_eq (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) hi
    have := C8144.rel_one (mem_getD (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (by omega : i < 37))
    have e : encW ((coverRels 0 0 0).getD i [] ++ zInv k) =
        encW ((coverRels 0 0 0).getD i []) ++ encW (zInv k) := List.map_append ..
    rw [hk, e, C8144.sword_append', hzinv, mul_one] at this
    exact this
  have hgen : Subgroup.closure (gen '' {g | g < 7}) = ⊤ := by
    rw [eq_top_iff, ← closure_pgGen (coverRels e₁ e₂ e₃), Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    by_cases h7 : g < 7
    · exact Subgroup.subset_closure ⟨g, h7, rfl⟩
    · have hg' : g < 8 := hg
      have : g = 7 := by omega
      subst this
      have h1 : pgGen (coverRels e₁ e₂ e₃) 7 = 1 := hg7
      rw [h1]
      exact Subgroup.one_mem _
  exact card_le_of_ON_rels gen hrels hgen

end CertificateChecks.KernelMiscCoset.ONCover

end
