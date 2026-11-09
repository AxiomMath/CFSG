module

public import Certificates.Data.Kernel.ONanSmall.CVData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import Certificates.Kernel.ONanSmall.Data.M12A
public import Certificates.Kernel.ONanSmall.Data.M12AW
public import CFSG.Certificates.Kernel.ONanSmall.ProductsSublist
public import CFSG.Certificates.Kernel.ONanSmall.CVGlue
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public import CFSG.GH74.KGroups.PermCheck
public import Mathlib.Tactic.Group

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Certificates.Kernel.ONanSmall.M12A

open CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.Sporadic.Schreier CFSG.KD.ONS.M12A

@[expose, reducible] noncomputable def sig : CV 24 := cOf m12Sigma

@[expose, reducible] noncomputable def LA : List (CV 24) :=
  elemsC m12D ++ (elemsC m12D).map (sig * ·)

@[expose] noncomputable def el (d : List Nat) : CV 24 := (genA m12D sig d).getD 1

@[expose] noncomputable def reps : List (CV 24) := R.map el

@[expose] noncomputable def cents : List (List (CV 24)) := C.map (List.map el)

theorem one_mem : (1 : CV 24) ∈ LA := by decide +kernel

section PickKey

variable {M : Type*} [Group M] {D : Type*} {α β : Type*}

@[expose] def pickStep (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool) (key : M → ℕ)
    (gen : D → Option M) (t : M) (k : List M → List (ℕ × D) → Option α)
    (reps : List M) (W : List (ℕ × D)) : Option α :=
  if inv t then
    match W with
    | [] => none
    | (j, d) :: W' =>
      if j == reps.length then
        if reps.any (fun r => key r == key t) && L₀.any fun g => reps.any fun r => conj g t r
        then none
        else k (reps ++ [t]) W'
      else
        match gen d with
        | some g => if j < reps.length && conj g t (reps.getD j 1) then k reps W' else none
        | none => none
  else k reps W

@[expose] noncomputable def pickRunG (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (fin : List M → List (ℕ × D) → Option α)
    (reps xs : List M) (W : List (ℕ × D)) : Option α :=
  List.rec (motive := fun _ => List M → List (ℕ × D) → Option α) fin
    (fun t _ k => pickStep L₀ inv conj key gen t k) xs reps W

@[expose] noncomputable def pickRunK (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (reps xs : List M) (W : List (ℕ × D)) :
    Option (List M) :=
  pickRunG L₀ inv conj key gen (fun reps _ => some reps) reps xs W

theorem pickStep_bind (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool) (key : M → ℕ)
    (gen : D → Option M) (t : M) (k : List M → List (ℕ × D) → Option α) (f : α → Option β)
    (reps : List M) (W : List (ℕ × D)) :
    pickStep L₀ inv conj key gen t (fun r w => (k r w).bind f) reps W =
      (pickStep L₀ inv conj key gen t k reps W).bind f := by
  unfold pickStep
  by_cases hi : inv t = true
  · rw [ite_eq_left hi, ite_eq_left hi]
    match W with
    | [] => rfl
    | (j, d) :: W' =>
      simp only
      by_cases hj : (j == reps.length) = true
      · rw [ite_eq_left hj, ite_eq_left hj]
        split <;> rfl
      · rw [ite_eq_right hj, ite_eq_right hj]
        cases gen d with
        | none => rfl
        | some g =>
          simp only
          split <;> rfl
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem pickRunG_append (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (fin : List M → List (ℕ × D) → Option α) (ys : List M) :
    ∀ (xs reps : List M) (W : List (ℕ × D)),
      pickRunG L₀ inv conj key gen fin reps (xs ++ ys) W =
        pickRunG L₀ inv conj key gen (fun r w => pickRunG L₀ inv conj key gen fin r ys w)
          reps xs W
  | [], _, _ => rfl
  | t :: xs, reps, W => by
    have e : (fun r w => pickRunG L₀ inv conj key gen fin r (xs ++ ys) w) =
        fun r w => pickRunG L₀ inv conj key gen
          (fun r w => pickRunG L₀ inv conj key gen fin r ys w) r xs w :=
      funext fun r => funext fun w => pickRunG_append L₀ inv conj key gen fin ys xs r w
    exact congrArg (fun k => pickStep L₀ inv conj key gen t k reps W) e

theorem pickRunG_bind (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (fin : List M → List (ℕ × D) → Option α) :
    ∀ (xs reps : List M) (W : List (ℕ × D)),
      pickRunG L₀ inv conj key gen fin reps xs W =
        (pickRunG L₀ inv conj key gen (fun r w => some (r, w)) reps xs W).bind
          fun p => fin p.1 p.2
  | [], _, _ => rfl
  | t :: xs, reps, W => by
    have e : (fun r w => pickRunG L₀ inv conj key gen fin r xs w) =
        fun r w => (pickRunG L₀ inv conj key gen (fun r w => some (r, w)) r xs w).bind
          fun p => fin p.1 p.2 :=
      funext fun r => funext fun w => pickRunG_bind L₀ inv conj key gen fin xs r w
    exact (congrArg (fun k => pickStep L₀ inv conj key gen t k reps W) e).trans
      (pickStep_bind L₀ inv conj key gen t _ _ reps W)

theorem pickRunG_chainL (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (fin : List M → List (ℕ × D) → Option α) :
    ∀ (cs : List (List M)) (k : ℕ) (st : ℕ → List M × List (ℕ × D)),
      (∀ i < cs.length, pickRunG L₀ inv conj key gen (fun r w => some (r, w)) (st (k + i)).1
        (cs.getD i []) (st (k + i)).2 = some (st (k + i + 1))) →
      pickRunG L₀ inv conj key gen fin (st k).1 cs.flatten (st k).2 =
        fin (st (k + cs.length)).1 (st (k + cs.length)).2
  | [], _, _, _ => rfl
  | c :: cs, k, st, h => by
    have h0 := h 0 (Nat.succ_pos _)
    rw [Nat.add_zero, List.getD_cons_zero] at h0
    rw [List.flatten_cons, pickRunG_append, pickRunG_bind, h0, Option.bind_some]
    have ih := pickRunG_chainL L₀ inv conj key gen fin cs (k + 1) st fun i hi => by
      have hs := h (i + 1) (by rw [List.length_cons]; omega)
      have e : k + 1 + i = k + (i + 1) := by omega
      rw [e]
      rwa [List.getD_cons_succ] at hs
    have e : k + 1 + cs.length = k + (c :: cs).length := by
      rw [List.length_cons]
      omega
    rw [ih, e]

theorem pickRunK_nil (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (reps : List M) (W : List (ℕ × D)) :
    pickRunK L₀ inv conj key gen reps [] W = some reps := rfl

theorem pickRunK_cons (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M) (reps : List M) (t : M) (ts : List M)
    (W : List (ℕ × D)) : pickRunK L₀ inv conj key gen reps (t :: ts) W =
      pickStep L₀ inv conj key gen t (fun reps W => pickRunK L₀ inv conj key gen reps ts W)
        reps W := rfl

theorem pickRun_of_pickRunK (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (key : M → ℕ) (gen : D → Option M)
    (hkey : ∀ g ∈ L₀, ∀ t ∈ L₀, ∀ r ∈ L₀, conj g t r = true → key t = key r) :
    ∀ (xs reps : List M) (W : List (ℕ × D)) (R : List M), (∀ x ∈ xs, x ∈ L₀) →
      (∀ r ∈ reps, r ∈ L₀) →
      pickRunK L₀ inv conj key gen reps xs W = some R → pickRun L₀ inv conj gen reps xs W = some R
  | [], reps, W, R, _, _, h => by
    rw [pickRunK_nil] at h
    unfold pickRun
    exact h
  | t :: ts, reps, W, R, hxs, hreps, h => by
    have hts : ∀ x ∈ ts, x ∈ L₀ := fun x hx => hxs x (List.mem_cons_of_mem t hx)
    have ht : t ∈ L₀ := hxs t List.mem_cons_self
    rw [pickRunK_cons] at h
    unfold pickStep at h
    unfold pickRun
    by_cases hi : inv t = true
    · rw [ite_eq_left hi] at h ⊢
      match W, h with
      | [], h => exact absurd h (by simp)
      | (j, d) :: W', h =>
        simp only at h ⊢
        by_cases hj : (j == reps.length) = true
        · rw [ite_eq_left hj] at h ⊢
          by_cases hs : (L₀.any fun g => reps.any fun r => conj g t r) = true
          · exfalso
            obtain ⟨g, hg, hr⟩ := List.any_eq_true.1 hs
            obtain ⟨r, hr, hc⟩ := List.any_eq_true.1 hr
            have hk : reps.any (fun r => key r == key t) = true :=
              List.any_eq_true.2 ⟨r, hr, by rw [hkey g hg t ht r (hreps r hr) hc, beq_self_eq_true]⟩
            rw [hk, hs] at h
            exact absurd h (by simp)
          · rw [ite_eq_right hs]
            rw [Bool.eq_false_iff.2 hs, Bool.and_false] at h
            refine pickRun_of_pickRunK L₀ inv conj key gen hkey ts _ W' R hts (fun r hr => ?_) h
            rcases List.mem_append.1 hr with hr | hr
            · exact hreps r hr
            · rw [List.mem_singleton.1 hr]
              exact ht
        · rw [ite_eq_right hj] at h ⊢
          cases hg : gen d with
          | none =>
            rw [hg] at h
            exact absurd h (by simp)
          | some g =>
            rw [hg] at h
            simp only at h ⊢
            by_cases hk : (j < reps.length && conj g t (reps.getD j 1)) = true
            · rw [ite_eq_left hk] at h ⊢
              exact pickRun_of_pickRunK L₀ inv conj key gen hkey ts reps W' R hts hreps h
            · rw [ite_eq_right hk] at h
              exact absurd h (by simp)
    · rw [ite_eq_right hi] at h ⊢
      exact pickRun_of_pickRunK L₀ inv conj key gen hkey ts reps W R hts hreps h

theorem mem_normalizer_of {G : Type*} [Group G] (H : Subgroup G) (s : G)
    (hn : ∀ h ∈ H, s * h * s⁻¹ ∈ H) (hs2 : s * s ∈ H) : s ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hn h, fun hh => ?_⟩
  have e : h = (s * s)⁻¹ * (s * (s * h * s⁻¹) * s⁻¹) * (s * s) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hs2) (hn _ hh)) hs2

end PickKey


theorem genA_eq_genP_gen (Q : CFSG.Certificates.RawSchreierDatum 24) (σ : CV 24) (w : List ℕ) :
    genA Q σ w = genP ([1, σ] :: TsC Q) w := by
  match w with
  | [] => simp [genA, genP]
  | 0 :: d =>
    rw [genP_cons_zero]
    simp only [genA, one_mul, Option.map_id']
  | 1 :: d =>
    rw [genP_cons_succ, genP_cons_zero]
    rfl
  | (k + 2) :: d =>
    rw [genP_cons_succ, genP_cons_succ]
    simp [genA, genP]

theorem genA_eq_genP (w : List ℕ) : genA m12D sig w = genP ([1, sig] :: TsC m12D) w :=
  genA_eq_genP_gen m12D sig w

theorem LA_eq_gen (Q : CFSG.Certificates.RawSchreierDatum 24) (σ : CV 24) :
    elemsC Q ++ (elemsC Q).map (σ * ·) = productsOf ([1, σ] :: TsC Q) := by
  rw [productsOf_cons_cons, productsOf_cons_cons, ← elemsC_eq]
  simp [productsOf]

theorem LA_eq : LA = productsOf ([1, sig] :: TsC m12D) := LA_eq_gen m12D sig

theorem length_productsOf {M : Type*} [Group M] :
    ∀ Ts : List (List M), (productsOf Ts).length = (Ts.map List.length).prod
  | [] => rfl
  | [] :: Ts => by simp [productsOf]
  | (t :: T) :: Ts => by
    rw [productsOf_cons_cons, List.length_append, List.length_map, length_productsOf Ts,
      length_productsOf (T :: Ts)]
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.succ_mul]
    exact Nat.add_comm _ _

theorem LA_length : LA.length = 190080 := by
  have h := congrArg List.length (elemsT_eq_elemsC m12D)
  rw [List.length_map, CFSG.GH74.KGroups.elemsT_eq, length_enumeration, m12D_check.2] at h
  rw [LA, List.length_append, List.length_map, ← h]

theorem sig_not_mem : m12Sigma ∉ m12D.originalSubgroup := by
  intro h
  refine m12D_sigma_outer m12Sigma⁻¹ (inv_mem h) fun k _ => ?_
  rw [mul_inv_cancel, one_mul, mul_one]

theorem mem_elemsC_iff (y : CV 24) : y ∈ elemsC m12D ↔ ev y ∈ m12D.originalSubgroup := by
  rw [← CFSG.GH74.KGroups.mem_elemsT m12D m12D_check.1, elemsT_eq_elemsC, List.mem_map]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [ev_injective hzy] at hz

theorem mem_LA_iff (x : CV 24) : x ∈ LA ↔
    ev x ∈ m12D.originalSubgroup ∨ m12Sigma⁻¹ * ev x ∈ m12D.originalSubgroup := by
  rw [LA, List.mem_append, mem_elemsC_iff, List.mem_map]
  refine or_congr Iff.rfl ⟨?_, fun h => ⟨sig⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_elemsC_iff] at hy
    rwa [ev_mul, ev_cOf, inv_mul_cancel_left]
  · rwa [mem_elemsC_iff, ev_mul, ev_inv, ev_cOf]

theorem LA_mul : ∀ a ∈ LA, ∀ b ∈ LA, a * b ∈ LA := by
  intro a ha b hb
  have hn := m12D_sigma_normalizes
  have hs2 := m12D_sigma_sq
  have hn' : ∀ h ∈ m12D.originalSubgroup, m12Sigma⁻¹ * h * m12Sigma ∈ m12D.originalSubgroup :=
    fun h hh => by
      have e : m12Sigma⁻¹ * h * m12Sigma =
          (m12Sigma * m12Sigma)⁻¹ * (m12Sigma * h * m12Sigma⁻¹) * (m12Sigma * m12Sigma) := by
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hs2) (hn h hh)) hs2
  rw [mem_LA_iff] at ha hb ⊢
  rw [ev_mul]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (mul_mem ha hb)
  · refine Or.inr ?_
    have e : m12Sigma⁻¹ * (ev a * ev b) = (m12Sigma⁻¹ * ev a * m12Sigma) * (m12Sigma⁻¹ * ev b) := by
      group
    rw [e]
    exact mul_mem (hn' _ ha) hb
  · refine Or.inr ?_
    rw [← mul_assoc]
    exact mul_mem ha hb
  · refine Or.inl ?_
    have e : ev a * ev b = (m12Sigma * m12Sigma) *
        (m12Sigma⁻¹ * (m12Sigma⁻¹ * ev a) * m12Sigma) * (m12Sigma⁻¹ * ev b) := by
      group
    rw [e]
    exact mul_mem (mul_mem hs2 (hn' _ ha)) hb

theorem LA_nodup_gen (Q : CFSG.Certificates.RawSchreierDatum 24)
    (hQ : CFSG.Certificates.ValidSchreier Q) (σ : Equiv.Perm (Fin 24))
    (hσ : σ ∉ Q.originalSubgroup) : (elemsC Q ++ (elemsC Q).map (cOf σ * ·)).Nodup := by
  refine List.Nodup.of_map (evHom 24) ?_
  rw [← elemsT_append_map]
  refine List.Nodup.append (CFSG.GH74.KGroups.nodup_elemsT Q hQ)
    ((CFSG.GH74.KGroups.nodup_elemsT Q hQ).map (mul_right_injective σ)) ?_
  intro a ha hb
  obtain ⟨b, hbT, rfl⟩ := List.mem_map.1 hb
  have h := mul_mem ((CFSG.GH74.KGroups.mem_elemsT Q hQ _).1 ha)
    (inv_mem ((CFSG.GH74.KGroups.mem_elemsT Q hQ b).1 hbT))
  rw [mul_inv_cancel_right] at h
  exact hσ h

theorem LA_nodup : LA.Nodup := LA_nodup_gen m12D m12D_check.1 m12Sigma sig_not_mem

theorem conj_mem_elemsC (g : CV 24) (hg : g ∈ LA) (x : CV 24) :
    g * x * g⁻¹ ∈ elemsC m12D ↔ x ∈ elemsC m12D := by
  have hs : m12Sigma ∈ Subgroup.normalizer (m12D.originalSubgroup : Set (Equiv.Perm (Fin 24))) :=
    mem_normalizer_of _ _ m12D_sigma_normalizes m12D_sigma_sq
  have hN : ev g ∈ Subgroup.normalizer (m12D.originalSubgroup : Set (Equiv.Perm (Fin 24))) := by
    rcases (mem_LA_iff g).1 hg with h | h
    · exact Subgroup.le_normalizer h
    · rw [← mul_inv_cancel_left m12Sigma (ev g)]
      exact mul_mem hs (Subgroup.le_normalizer h)
  rw [mem_elemsC_iff, mem_elemsC_iff, ev_mul, ev_mul, ev_inv]
  exact ((Subgroup.mem_normalizer_iff.1 hN) (ev x)).symm

@[expose] noncomputable def keyA (x : CV 24) : ℕ :=
  (ev x).support.card + if (ev x 0).val < 12 then 100 else 0

open scoped Pointwise

@[expose] def m12Blk : Finset (Fin 24) := Finset.univ.filter fun i => i.val < 12

theorem m12_le_stab :
    m12D.originalSubgroup ≤ MulAction.stabilizer (Equiv.Perm (Fin 24)) m12Blk := by
  rw [m12D, CFSG.Sporadic.Schreier.certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    decide +kernel
  · rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    decide +kernel

theorem lt_of_mem_m12 (m : Equiv.Perm (Fin 24)) (hm : m ∈ m12D.originalSubgroup) (i : Fin 24)
    (hi : i.val < 12) : (m i).val < 12 := by
  have h := MulAction.mem_stabilizer_iff.1 (m12_le_stab hm)
  have hmem : m • i ∈ m • m12Blk :=
    Finset.smul_mem_smul_finset (by simp [m12Blk, hi])
  rw [h] at hmem
  simpa [m12Blk] using hmem

theorem sig_ge12 : ∀ i : Fin 24, i.val < 12 → 12 ≤ (m12Sigma i).val := by
  decide +kernel

theorem mem_elemsC_iff_lt (x : CV 24) (hx : x ∈ LA) :
    x ∈ elemsC m12D ↔ (ev x 0).val < 12 := by
  rw [mem_elemsC_iff]
  rcases (mem_LA_iff x).1 hx with h | h
  · exact iff_of_true h (lt_of_mem_m12 _ h 0 (by decide))
  · refine iff_of_false (fun h' => sig_not_mem ?_) ?_
    · have h2 := mul_mem h' (inv_mem h)
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h2
    · have e : ev x 0 = m12Sigma ((m12Sigma⁻¹ * ev x) 0) := by
        simp [Equiv.Perm.mul_apply]
      rw [e]
      exact Nat.not_lt.2 (sig_ge12 _ (lt_of_mem_m12 _ h 0 (by decide)))

theorem keyA_conj : ∀ g ∈ LA, ∀ t ∈ LA, ∀ r ∈ LA, conjC g t r = true → keyA t = keyA r := by
  intro g hg t ht r hr h
  have hk : ∀ y ∈ LA, keyA y = (ev y).support.card + if y ∈ elemsC m12D then 100 else 0 :=
    fun y hy => by simp only [keyA, mem_elemsC_iff_lt y hy]
  rw [hk t ht, hk r hr]
  rw [conjC, eq22C_eq, decide_eq_true_iff] at h
  rw [eq_mul_inv_of_mul_eq h.symm]
  simp only [ev_mul, ev_inv, Equiv.Perm.card_support_conj, conj_mem_elemsC g hg t]

@[expose] def pickRA : List ℕ := [0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3]

@[expose] def pickWA : List ℕ := [0, 165, 231, 297, 363, 429, 495, 561, 627, 693, 759, 825, 891, 957,
  1023, 1089, 1155, 1221, 1287, 1353, 1419, 1485, 1551, 1617, 1683]

@[expose] noncomputable def pickSt (i : ℕ) : List (CV 24) × List (ℕ × List ℕ) :=
  (reps.take (pickRA.getD i 0), W.drop (pickWA.getD i 0))

@[expose] noncomputable def pickCs : List (List (CV 24)) :=
  match TsC m12D with
  | [] => []
  | T1 :: Ts => T1.map (fun t => (productsOf Ts).map (t * ·)) ++
      T1.map (fun t => ((productsOf Ts).map (t * ·)).map (sig * ·))

theorem LA_flatten : LA = pickCs.flatten := by
  have hne : TsC m12D ≠ [] := by decide +kernel
  rw [LA, elemsC_eq]
  unfold pickCs
  match h : TsC m12D, hne with
  | T1 :: Ts, _ =>
    simp [productsOf, List.flatMap_def, List.map_flatten, Function.comp_def]

theorem pickCs_length : pickCs.length = 24 := by decide +kernel

@[expose, reducible] noncomputable def pickChunk (i : ℕ) : Prop :=
  pickRunG LA invC conjC keyA (genA m12D sig) (fun r w => some (r, w)) (pickSt i).1
    (pickCs.getD i []) (pickSt i).2 = some (pickSt (i + 1))

theorem pick0 : pickChunk 0 := by decide +kernel
theorem pick1 : pickChunk 1 := by decide +kernel
theorem pick2 : pickChunk 2 := by decide +kernel
theorem pick3 : pickChunk 3 := by decide +kernel
theorem pick4 : pickChunk 4 := by decide +kernel
theorem pick5 : pickChunk 5 := by decide +kernel
theorem pick6 : pickChunk 6 := by decide +kernel
theorem pick7 : pickChunk 7 := by decide +kernel
theorem pick8 : pickChunk 8 := by decide +kernel
theorem pick9 : pickChunk 9 := by decide +kernel
theorem pick10 : pickChunk 10 := by decide +kernel
theorem pick11 : pickChunk 11 := by decide +kernel
theorem pick12 : pickChunk 12 := by decide +kernel
theorem pick13 : pickChunk 13 := by decide +kernel
theorem pick14 : pickChunk 14 := by decide +kernel
theorem pick15 : pickChunk 15 := by decide +kernel
theorem pick16 : pickChunk 16 := by decide +kernel
theorem pick17 : pickChunk 17 := by decide +kernel
theorem pick18 : pickChunk 18 := by decide +kernel
theorem pick19 : pickChunk 19 := by decide +kernel
theorem pick20 : pickChunk 20 := by decide +kernel
theorem pick21 : pickChunk 21 := by decide +kernel
theorem pick22 : pickChunk 22 := by decide +kernel
theorem pick23 : pickChunk 23 := by decide +kernel

theorem pickChunk_all : ∀ i < 24, pickChunk i
  | 0, _ => pick0 | 1, _ => pick1 | 2, _ => pick2 | 3, _ => pick3 | 4, _ => pick4
  | 5, _ => pick5 | 6, _ => pick6 | 7, _ => pick7 | 8, _ => pick8 | 9, _ => pick9
  | 10, _ => pick10 | 11, _ => pick11 | 12, _ => pick12 | 13, _ => pick13 | 14, _ => pick14
  | 15, _ => pick15 | 16, _ => pick16 | 17, _ => pick17 | 18, _ => pick18 | 19, _ => pick19
  | 20, _ => pick20 | 21, _ => pick21 | 22, _ => pick22 | 23, _ => pick23
  | _ + 24, h => absurd h (by omega)

theorem reps_length : reps.length = 3 := by
  rw [reps, List.length_map]
  decide +kernel

theorem pick : pickRun LA invC conjC (genA m12D sig) [] LA W = some reps := by
  refine pickRun_of_pickRunK LA invC conjC keyA (genA m12D sig) keyA_conj LA [] W reps
    (fun _ hx => hx) (fun _ hr => absurd hr List.not_mem_nil) ?_
  have h := pickRunG_chainL LA invC conjC keyA (genA m12D sig) (fun r _ => some r) pickCs 0
    pickSt fun i hi => by
      rw [Nat.zero_add]
      exact pickChunk_all i (by rwa [pickCs_length] at hi)
  rw [← LA_flatten, pickCs_length, Nat.zero_add] at h
  have h0 : pickSt 0 = ([], W) := by
    simp only [pickSt, pickRA, pickWA, List.getD_cons_zero, List.take_zero, List.drop_zero]
  have h24 : (pickSt 24).1 = reps := by
    simp only [pickSt]
    exact List.take_of_length_le (by rw [reps_length]; decide)
  rw [h0, h24] at h
  exact h

@[expose] noncomputable def wx (j : ℕ) : List ((ℕ × List ℕ) × List ℕ) :=
  (W.zip X).filter fun p => p.1.1 == j

@[expose] noncomputable def conjOkB (rw : List ℕ) (p : (ℕ × List ℕ) × List ℕ) : Bool :=
  (genA m12D sig p.1.2).isSome && (genA m12D sig p.2).isSome &&
    eq22C (el p.1.2) (el p.2) (el rw) (el p.1.2)

theorem zip_snd_sublist {α β : Type*} : ∀ (l₁ : List α) (l₂ : List β),
    ((l₁.zip l₂).map Prod.snd).Sublist l₂
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
    rw [List.zip_cons_cons, List.map_cons]
    exact (zip_snd_sublist l₁ l₂).cons_cons b

@[expose] def lexChainB : List (List ℕ) → Bool
  | a :: b :: l => decide (a < b) && lexChainB (b :: l)
  | _ => true

theorem lexChainB_pairwise : ∀ ws : List (List ℕ), lexChainB ws = true →
    ws.Pairwise (List.Lex (· < ·))
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    rw [lexChainB, Bool.and_eq_true] at h
    have ih := lexChainB_pairwise (b :: l) h.2
    have hab : a < b := of_decide_eq_true h.1
    refine List.pairwise_cons.2 ⟨fun c hc => ?_, ih⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact List.lt_trans hab (List.rel_of_pairwise_cons ih hc)

theorem X_chain : lexChainB X = true := by decide +kernel

@[expose] noncomputable def centOkB (j : ℕ) (rw : List ℕ) (cw : List (List ℕ)) : Bool :=
  cw.all (fun d => (genA m12D sig d).isSome) && lexChainB cw &&
    (cw.map el).all (fun x => eq22C x (el rw) (el rw) x) && (wx j).all (conjOkB rw) &&
    decide (190080 ≤ (wx j).length * cw.length)

@[expose] noncomputable def centAllB : ℕ → List (List ℕ) → List (List (List ℕ)) → Bool
  | j, rw :: R, cw :: C => centOkB j rw cw && centAllB (j + 1) R C
  | _, [], [] => true
  | _, _, _ => false

theorem map_el_eq : ∀ cw : List (List ℕ), cw.all (fun d => (genA m12D sig d).isSome) = true →
    cw.map el = cw.filterMap (genA m12D sig)
  | [], _ => rfl
  | d :: cw, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h.1
    have he : el d = g := by simp [el, hg]
    rw [List.map_cons, List.filterMap_cons_some hg, map_el_eq cw h.2, he]

theorem centOkB_sound (j : ℕ) (rw : List ℕ) (cw : List (List ℕ)) (h : centOkB j rw cw = true) :
    centC LA (el rw) = cw.map el := by
  simp only [centOkB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hv, hc⟩, hcomm⟩, hcj⟩, hcard⟩ := h
  have hcard' := of_decide_eq_true hcard
  have hf : genA m12D sig = genP ([1, sig] :: TsC m12D) := funext genA_eq_genP
  have hp : ∀ p ∈ wx j, conjOkB rw p = true := List.all_eq_true.1 hcj
  have hws : ((wx j).map Prod.snd).all (fun d => (genA m12D sig d).isSome) = true := by
    refine List.all_eq_true.2 fun d hd => ?_
    obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hd
    have h := hp p hpm
    simp only [conjOkB, Bool.and_eq_true] at h
    exact h.1.2
  have hsub : ∀ ws : List (List ℕ), ws.all (fun d => (genA m12D sig d).isSome) = true →
      ws.Pairwise (List.Lex (· < ·)) → (ws.map el).Sublist LA := fun ws hv hc => by
    rw [map_el_eq ws hv, hf, LA_eq]
    exact sublist_productsOf _ _ hc (fun w hw => by rw [← hf]; exact List.all_eq_true.1 hv w hw)
  have hXs : ((wx j).map Prod.snd).Sublist X :=
    (List.filter_sublist.map Prod.snd).trans (zip_snd_sublist W X)
  rw [← centB_eq_centC]
  refine centB_eq_of_length LA (((wx j).map Prod.snd).map el) (cw.map el) (el rw) LA_nodup
    (LA_nodup.sublist (hsub _ hws ((lexChainB_pairwise X X_chain).sublist hXs))) LA_mul ?_
    (hsub cw hv (lexChainB_pairwise cw hc)) ?_ ?_ ?_
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hd
    have h := hp p hpm
    simp only [conjOkB, Bool.and_eq_true] at h
    obtain ⟨⟨hg, -⟩, he⟩ := h
    obtain ⟨g, hg'⟩ := Option.isSome_iff_exists.1 hg
    have hge : el p.1.2 = g := by simp [el, hg']
    rw [eq22C_eq] at he
    refine ⟨el p.1.2, hge ▸ genA_mem _ _ _ g hg', ?_⟩
    rw [of_decide_eq_true he, mul_inv_cancel_right]
  · intro x hx
    have hx' := List.all_eq_true.1 hcomm x hx
    rw [eq22C_eq] at hx'
    exact of_decide_eq_true hx'
  · rw [LA_length, List.length_map, List.length_map, List.length_map]
    exact hcard'
  · rw [List.length_map, List.length_map]
    rcases Nat.eq_zero_or_pos (wx j).length with h0 | h0
    · rw [h0, Nat.zero_mul] at hcard'
      omega
    · exact h0

theorem centAllB_sound : ∀ (j : ℕ) (R : List (List ℕ)) (C : List (List (List ℕ))),
    centAllB j R C = true → (R.map el).map (centC LA) = C.map (List.map el)
  | j, rw :: R, cw :: C, h => by
    rw [centAllB, Bool.and_eq_true] at h
    rw [List.map_cons, List.map_cons, List.map_cons, centOkB_sound j rw cw h.1,
      centAllB_sound (j + 1) R C h.2]
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by simp [centAllB] at h
  | _, _ :: _, [], h => by simp [centAllB] at h

theorem cent_check : centAllB 0 R C = true := by decide +kernel

theorem cent_ok : reps.map (centC LA) = cents := centAllB_sound 0 R C cent_check

section Wit

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def ordIt (o : M) : ℕ → M → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, y, k => if y = 1 then k else ordIt o f (y * o) (k + 1)

theorem ordIt_eq (o : M) : ∀ f k, ordIt o f (o ^ k) k = ordAux o f k
  | 0, _ => rfl
  | f + 1, k => by
    rw [ordIt, ordAux, ← pow_succ, ordIt_eq o f (k + 1)]

theorem ordB_eq_ordIt (B : ℕ) (o : M) : ordB B o = ordIt o B o 1 := by
  rw [ordB, ← ordIt_eq o B 1, pow_one]

@[expose] def evenOrdIt (B : ℕ) (x : M) : Bool :=
  decide (ordIt x B x 1 ≠ 0) && decide (ordIt x B x 1 % 2 = 0)

@[expose] def oddWitB (B : ℕ) (C : List M) (o : M) : List ℕ → Bool
  | [i] => decide (i < C.length) && evenOrdIt B (o * (C.getD i 1 * o * (C.getD i 1)⁻¹))
  | [i, j] => decide (i < C.length) && decide (j < C.length) &&
      evenOrdIt B (o * (C.getD i 1 * o * (C.getD i 1)⁻¹) * (C.getD j 1 * o * (C.getD j 1)⁻¹))
  | _ => false

@[expose] def oddOk (B : ℕ) (C : List M) (o : M) (w : List ℕ) : Bool :=
  decide (ordIt o B o 1 ≠ 0) &&
    (decide (o = 1) || decide (ordIt o B o 1 % 2 = 0) || oddWitB B C o w)

@[expose] def pairsW (t : M) (C : List M) (pw : List (ℕ × ℕ × ℕ)) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) || pw.any fun p =>
        decide (C.getD p.1 1 = a) && decide (C.getD p.2.1 1 = b) && decide (p.2.2 < C.length) &&
          !(memB (q8B t a b) (C.getD p.2.2 1 * a * (C.getD p.2.2 1)⁻¹) &&
            memB (q8B t a b) (C.getD p.2.2 1 * b * (C.getD p.2.2 1)⁻¹))

theorem exists_mem_zip_of_mem {α β : Type*} {o : α} :
    ∀ (C : List α) (ws : List β), C.length = ws.length → o ∈ C → ∃ w, (o, w) ∈ C.zip ws
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | x :: C, w :: ws, hl, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨w, by simp⟩
    · obtain ⟨w', hw'⟩ := exists_mem_zip_of_mem C ws (by simpa using hl) h
      exact ⟨w', by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hw'⟩

omit [DecidableEq M] in
theorem getD_one_mem_list (C : List M) (i : ℕ) (h : i < C.length) : C.getD i 1 ∈ C := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem noOddB3_of_wit (B : ℕ) (C : List M) (ws : List (List ℕ)) (hl : C.length = ws.length)
    (h : (C.zip ws).all (fun p => oddOk B C p.1 p.2) = true) : noOddB3 B C = true := by
  unfold noOddB3
  rw [List.all_eq_true]
  intro o ho
  obtain ⟨w, hw⟩ := exists_mem_zip_of_mem C ws hl ho
  have h1 := List.all_eq_true.1 h _ hw
  simp only [oddOk, ← ordB_eq_ordIt, Bool.and_eq_true, Bool.or_eq_true] at h1
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨h1.1, ?_⟩
  rcases h1.2 with h2 | h2
  · exact Or.inl (Or.inl h2)
  · match w, h2 with
    | [i], h2 =>
      simp only [oddWitB, evenOrdIt, ← ordB_eq_ordIt, Bool.and_eq_true] at h2
      refine Or.inl (Or.inr (List.any_eq_true.2 ⟨_, getD_one_mem_list C i (of_decide_eq_true h2.1), ?_⟩))
      rw [Bool.and_eq_true]
      exact h2.2
    | [i, j], h2 =>
      simp only [oddWitB, evenOrdIt, ← ordB_eq_ordIt, Bool.and_eq_true] at h2
      refine Or.inr (List.any_eq_true.2 ⟨_, getD_one_mem_list C i (of_decide_eq_true h2.1.1),
        List.any_eq_true.2 ⟨_, getD_one_mem_list C j (of_decide_eq_true h2.1.2), ?_⟩⟩)
      rw [Bool.and_eq_true]
      exact h2.2
    | [], h2 => simp [oddWitB] at h2
    | _ :: _ :: _ :: _, h2 => simp [oddWitB] at h2

theorem pairsV_of_wit (B : ℕ) (LN L : List M) (e3b : Bool) (t : M) (C : List M)
    (pw : List (ℕ × ℕ × ℕ)) (h : pairsW t C pw = true) : pairsV B LN L e3b t C = true := by
  unfold pairsV
  unfold pairsW at h
  rw [List.all_eq_true] at h ⊢
  intro a ha
  have h1 := h a ha
  rw [List.all_eq_true] at h1 ⊢
  intro b hb
  have h2 := h1 b hb
  rw [Bool.or_eq_true] at h2
  simp only [Bool.or_eq_true]
  rcases h2 with h2 | h2
  · exact Or.inl (Or.inl (Or.inl (Or.inl h2)))
  · obtain ⟨p, -, hp⟩ := List.any_eq_true.1 h2
    simp only [Bool.and_eq_true] at hp
    obtain ⟨-, hk⟩ := hp.1
    have hn := hp.2
    refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
    have hf : (C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)) =
        false := List.all_eq_false.2 ⟨_, getD_one_mem_list C p.2.2 (of_decide_eq_true hk), fun hc => by
          rw [hc] at hn
          exact absurd hn (by decide)⟩
    rw [hf]
    rfl

end Wit

theorem k9748_len : (reps.zip cents).length = (oddWit.zip q8Wit).length := by
  decide +kernel

theorem k9748W : ((reps.zip cents).zip (oddWit.zip q8Wit)).all (fun q =>
    decide (q.1.2.length = q.2.1.length) &&
      (q.1.2.zip q.2.1).all (fun p => oddOk 100 q.1.2 p.1 p.2) && pairsW q.1.1 q.1.2 q.2.2) =
    true := by
  decide +kernel

theorem k9748 : (reps.zip cents).all (fun p => noOddB3 100 p.2 &&
    pairsV 100 (elemsC m12D) LA false p.1 p.2) = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨w, hw⟩ := exists_mem_zip_of_mem _ _ k9748_len hp
  have h := List.all_eq_true.1 k9748W _ hw
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨noOddB3_of_wit 100 p.2 w.1 (of_decide_eq_true h.1.1) h.1.2,
    pairsV_of_wit _ _ _ _ _ _ _ h.2⟩

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM in
theorem k397508 : (reps.zip cents).all (fun p =>
    nqAt (fun x => firstBlock (ev x)) p.1 p.2) = true := by
  decide +kernel

end Certificates.Kernel.ONanSmall.M12A
