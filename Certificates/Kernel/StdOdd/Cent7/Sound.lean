module

public import Certificates.Data.Kernel.Misc.E6SubClos
public import Certificates.Kernel.StdOdd.Comm7B.Sound

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

attribute [local irreducible] mulB

theorem letL_eq (l : List ℕ) (k : List ℕ → Bool) : letL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    change letB x (fun x => letL l fun ys => k (x :: ys)) = k (x :: l)
    rw [letB_eq', ih]

theorem conjStepThenK_sound (P : ℕ → Prop) (G Gi : ℕ → ℕ) (k : List ℕ → Bool)
    (hP : ∀ N j, P N → P (mulB (mulB (G j) N) (Gi j))) :
    ∀ (steps : List (ℕ × ℕ)) (acc : List ℕ), (∀ N ∈ acc, P N) → acc.Nodup →
      conjStepThenK G Gi steps k acc = true →
        ∃ L : List ℕ, L.Nodup ∧ L.length = acc.length + steps.length ∧ acc <+: L ∧
          (∀ N ∈ L, P N) ∧ k L = true := by
  intro steps
  induction steps with
  | nil => exact fun acc hacc hnd h => ⟨acc, hnd, rfl, List.prefix_refl _, hacc, h⟩
  | cons s steps ih =>
    intro acc hacc hnd h
    obtain ⟨p, j⟩ := s
    have e : conjStepThenK G Gi ((p, j) :: steps) k acc = andB (Nat.blt p (lenN acc))
        (letB (mulB (mulB (G j) (nthV acc p)) (Gi j)) fun y =>
          andB (notB (memN y acc)) (conjStepThenK G Gi steps k (snocN acc y))) := rfl
    rw [e, letB_eq', andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true, notB_eq',
      Bool.not_eq_true', Nat.blt_eq, lenN_eq_length] at h
    obtain ⟨hp, hmem, hrest⟩ := h
    have hy : mulB (mulB (G j) (nthV acc p)) (Gi j) ∉ acc := by
      rw [← memN_eq_true_iff, hmem]
      exact Bool.false_ne_true
    have hPy : P (mulB (mulB (G j) (nthV acc p)) (Gi j)) := by
      refine hP _ j (hacc _ ?_)
      rw [nthV_eq_getD, List.getD_eq_getElem _ _ hp]
      exact List.getElem_mem hp
    rw [snocN_eq] at hrest
    obtain ⟨L, hL, hlen, hpre, hPL, hk⟩ := ih (acc ++ [mulB (mulB (G j) (nthV acc p)) (Gi j)])
      (fun N hN => by
        rcases List.mem_append.1 hN with hN | hN
        · exact hacc N hN
        · rw [List.mem_singleton.1 hN]
          exact hPy)
      (List.nodup_append.2 ⟨hnd, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.1 hb]
        rintro rfl
        exact hy ha⟩) hrest
    refine ⟨L, hL, ?_, (List.prefix_append _ _).trans hpre, hPL, hk⟩
    rw [hlen, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem conjOrbThenK_sound (P : ℕ → Prop) {a ai b bi z : ℕ} {steps : List (ℕ × ℕ)}
    {k : List ℕ → Bool} (hz : P z) (ha : ∀ N, P N → P (mulB (mulB a N) ai))
    (hb : ∀ N, P N → P (mulB (mulB b N) bi)) (h : conjOrbThenK a ai b bi steps z k = true) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = 1 + steps.length ∧ [z] <+: L ∧ (∀ N ∈ L, P N) ∧
      k L = true := by
  unfold conjOrbThenK at h
  rw [letB_eq', letB_eq', letB_eq', letB_eq', letB_eq'] at h
  have hP : ∀ N j, P N → P (mulB (mulB (Bool.rec (motive := fun _ => ℕ) b a (Nat.beq j 0)) N)
      (Bool.rec (motive := fun _ => ℕ) bi ai (Nat.beq j 0))) := by
    intro N j hN
    cases Nat.beq j 0
    · exact hb N hN
    · exact ha N hN
  have := conjStepThenK_sound P _ _ k hP steps [z] (fun N hN => by
    rw [List.mem_singleton.1 hN]
    exact hz) (List.nodup_singleton z) h
  simpa only [List.length_singleton] using this

theorem mulStepK_sound (P : ℕ → Prop) (G : ℕ → ℕ) (n : ℕ) (k : List ℕ → Bool)
    (hP : ∀ N j, j < n → P N → P (mulB N (G j))) :
    ∀ (steps : List (ℕ × ℕ)) (acc : List ℕ), (∀ N ∈ acc, P N) → acc.Nodup →
      mulStepK G n steps k acc = true →
        ∃ L : List ℕ, L.Nodup ∧ L.length = acc.length + steps.length ∧ acc <+: L ∧
          (∀ N ∈ L, P N) ∧ k L = true := by
  intro steps
  induction steps with
  | nil => exact fun acc hacc hnd h => ⟨acc, hnd, rfl, List.prefix_refl _, hacc, h⟩
  | cons s steps ih =>
    intro acc hacc hnd h
    obtain ⟨p, j⟩ := s
    have e : mulStepK G n ((p, j) :: steps) k acc = andB (Nat.blt j n) (andB
        (Nat.blt p (lenN acc)) (letB (mulB (nthV acc p) (G j)) fun y =>
          andB (notB (memN y acc)) (mulStepK G n steps k (snocN acc y)))) := rfl
    rw [e, letB_eq', andB_eq', andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, notB_eq', Bool.not_eq_true', Nat.blt_eq, Nat.blt_eq, lenN_eq_length] at h
    obtain ⟨hj, hp, hmem, hrest⟩ := h
    have hy : mulB (nthV acc p) (G j) ∉ acc := by
      rw [← memN_eq_true_iff, hmem]
      exact Bool.false_ne_true
    have hPy : P (mulB (nthV acc p) (G j)) := by
      refine hP _ j hj (hacc _ ?_)
      rw [nthV_eq_getD, List.getD_eq_getElem _ _ hp]
      exact List.getElem_mem hp
    rw [snocN_eq] at hrest
    obtain ⟨L, hL, hlen, hpre, hPL, hk⟩ := ih (acc ++ [mulB (nthV acc p) (G j)])
      (fun N hN => by
        rcases List.mem_append.1 hN with hN | hN
        · exact hacc N hN
        · rw [List.mem_singleton.1 hN]
          exact hPy)
      (List.nodup_append.2 ⟨hnd, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.1 hb]
        rintro rfl
        exact hy ha⟩) hrest
    refine ⟨L, hL, ?_, (List.prefix_append _ _).trans hpre, hPL, hk⟩
    rw [hlen, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem subClosK_sound {H : Type*} [Group H] [Finite H] (R : ℕ → H → Prop)
    (hmul : ∀ {a b : ℕ} {x y : H}, R a x → R b y → R (mulB a b) (x * y)) (hone : R oneB 1)
    (hinj : ∀ {a b : ℕ} {x y : H}, R a x → R b y → (a = b ↔ x = y))
    {gens : List ℕ} {g : ℕ → H} (hg : ∀ j < gens.length, R (nthV gens j) (g j))
    {steps : List (ℕ × ℕ)} {k : List ℕ → Bool} (h : subClosK gens steps k = true) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = 1 + steps.length ∧ k L = true ∧
      (∀ N ∈ L, ∃ x ∈ Subgroup.closure {x | ∃ j < gens.length, g j = x}, R N x) ∧
      (∀ x ∈ Subgroup.closure {x | ∃ j < gens.length, g j = x}, ∃ N ∈ L, R N x) ∧
      Nat.card (Subgroup.closure {x | ∃ j < gens.length, g j = x}) = 1 + steps.length := by
  classical
  set Q := Subgroup.closure {x | ∃ j < gens.length, g j = x} with hQ
  unfold subClosK at h
  rw [letL_eq, letB_eq', lenN_eq_length] at h
  let P : ℕ → Prop := fun N => ∃ x ∈ Q, R N x
  have hP : ∀ N j, j < gens.length → P N → P (mulB N (nthV gens j)) := by
    rintro N j hj ⟨x, hx, hNx⟩
    exact ⟨x * g j, Q.mul_mem hx (Subgroup.subset_closure ⟨j, hj, rfl⟩), hmul hNx (hg j hj)⟩
  obtain ⟨L, hnd, hlen, hpre, hPL, hk⟩ := mulStepK_sound P _ _ _ hP steps [oneB]
    (fun N hN => by
      rw [List.mem_singleton.1 hN]
      exact ⟨1, Q.one_mem, hone⟩) (List.nodup_singleton _) h
  rw [andB_eq', Bool.and_eq_true] at hk
  obtain ⟨hcl, hk⟩ := hk
  have hcl' : ∀ N ∈ L, ∀ j < gens.length, mulB N (nthV gens j) ∈ L := by
    intro N hN j hj
    have hm : nthV gens j ∈ gens := by
      rw [nthV_eq_getD, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    rw [← memN_eq_true_iff]
    exact allL_true (allL_true hcl N hN) _ hm
  have h1 : oneB ∈ L := hpre.subset (List.mem_singleton_self _)
  let T : Set H := {x | ∃ N ∈ L, R N x}
  let M : Submonoid H :=
    { carrier := {y | ∀ z ∈ T, z * y ∈ T}
      one_mem' := fun z hz => by rw [mul_one]; exact hz
      mul_mem' := fun {a b} ha hb z hz => by rw [← mul_assoc]; exact hb _ (ha z hz) }
  have hpow : ∀ y ∈ M, ∀ n : ℕ, y ^ n ∈ M := fun y hy n => M.pow_mem hy n
  let S : Subgroup H :=
    { M with
      inv_mem' := fun {y} hy => by
        have hpos := orderOf_pos y
        have e : y⁻¹ = y ^ (orderOf y - 1) := by
          refine (eq_inv_of_mul_eq_one_left ?_).symm
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [e]
        exact hpow y hy _ }
  have hQS : Q ≤ S := by
    rw [hQ, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩ z ⟨N, hN, hNz⟩
    exact ⟨_, hcl' N hN j hj, hmul hNz (hg j hj)⟩
  have hcov : ∀ x ∈ Q, ∃ N ∈ L, R N x := by
    intro x hx
    have := hQS hx 1 ⟨oneB, h1, hone⟩
    rwa [one_mul] at this
  refine ⟨L, hnd, by rw [hlen, List.length_singleton], hk, hPL, hcov, ?_⟩
  let F : ℕ → H := fun N => if hN : ∃ x, R N x then hN.choose else 1
  have hF : ∀ N x, R N x → F N = x := by
    intro N x hNx
    have hN : ∃ x, R N x := ⟨x, hNx⟩
    simp only [F, dif_pos hN]
    exact (hinj hN.choose_spec hNx).1 rfl
  have hset : (Q : Set H) = ((L.toFinset.image F : Finset H) : Set H) := by
    ext x
    simp only [SetLike.mem_coe, Finset.coe_image, List.coe_toFinset, Set.mem_image,
      Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨N, hN, hNx⟩ := hcov x hx
      exact ⟨N, hN, hF N x hNx⟩
    · rintro ⟨N, hN, rfl⟩
      obtain ⟨x, hx, hNx⟩ := hPL N hN
      rw [hF N x hNx]
      exact hx
  have hinjF : Set.InjOn F (L.toFinset : Set ℕ) := by
    intro N hN N' hN' e
    rw [Finset.mem_coe, List.mem_toFinset] at hN hN'
    obtain ⟨x, -, hNx⟩ := hPL N hN
    obtain ⟨x', -, hNx'⟩ := hPL N' hN'
    rw [hF N x hNx, hF N' x' hNx'] at e
    exact (hinj hNx hNx').2 e
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    Finset.card_image_of_injOn hinjF, List.toFinset_card_of_nodup hnd, hlen,
    List.length_singleton]

theorem invInK_sound {Q L : List ℕ} (h : invInK Q L = true) :
    ∀ q ∈ Q, mulB q q = oneB → q = oneB ∨ q ∈ L := by
  intro q hq hsq
  unfold invInK at h
  rw [letB_eq'] at h
  have h1 := allL_true h q hq
  have e1 : Nat.beq (mulB q q) oneB = true := by rw [Nat.beq_eq]; exact hsq
  rw [e1] at h1
  change orB (Nat.beq q oneB) (memN q L) = true at h1
  cases h2 : Nat.beq q oneB
  · rw [h2] at h1
    change memN q L = true at h1
    exact Or.inr ((memN_eq_true_iff q L).1 h1)
  · exact Or.inl (by rw [Nat.beq_eq] at h2; exact h2)

section Rel

variable {H : Type*} [Group H] (R : ℕ → H → Prop)
  (hmul : ∀ {a b : ℕ} {x y : H}, R a x → R b y → R (mulB a b) (x * y)) (hone : R oneB 1)
  (hinj : ∀ {a b : ℕ} {x y : H}, R a x → R b y → (a = b ↔ x = y))
include hmul hone

theorem powB_sound {a : ℕ} {x : H} (ha : R a x) (n : ℕ) : R (powB a n) (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact hone
  | succ n ih =>
    change R (mulB (powB a n) a) (x ^ (n + 1))
    rw [pow_succ]
    exact hmul ih ha

theorem lineB_sound {ls : List ℕ} {X : ℕ → H} {n : ℕ} (hX : ∀ i < n, R (nthV ls i) (X i)) :
    ∀ w : List ℕ, (∀ i ∈ w, i < n) → R (lineB ls w) (w.map X).prod := by
  have key : ∀ (w : List ℕ), (∀ i ∈ w, i < n) → ∀ (acc : ℕ) (x : H), R acc x →
      R (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun i _ ih acc => ih (mulB acc (nthV ls i))) w acc) (x * (w.map X).prod) := by
    intro w
    induction w with
    | nil => intro _ acc x h; rw [List.map_nil, List.prod_nil, mul_one]; exact h
    | cons i w ih =>
      intro hw acc x h
      rw [List.map_cons, List.prod_cons, ← mul_assoc]
      exact ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _ _
        (hmul h (hX i (hw i List.mem_cons_self)))
  intro w hw
  have := key w hw oneB 1 hone
  rwa [one_mul] at this

theorem wordsB_sound {ls : List ℕ} {X : ℕ → H} {n : ℕ} (hX : ∀ i < n, R (nthV ls i) (X i)) :
    ∀ ws : List (List ℕ × ℕ), (∀ w ∈ ws, ∀ i ∈ w.1, i < n) → ∀ j < ws.length,
      R (nthV (wordsB ls ws) j) (((ws.getD j ([], 0)).1.map X).prod ^ (ws.getD j ([], 0)).2) := by
  intro ws
  induction ws with
  | nil => intro _ j hj; simp at hj
  | cons w ws ih =>
    intro hw j hj
    rcases j with _ | j
    · obtain ⟨l, e⟩ := w
      exact powB_sound R hmul hone (lineB_sound R hmul hone hX l (hw _ List.mem_cons_self)) e
    · exact ih (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) j
        (by simpa using hj)

omit hone in
include hinj in
theorem length_le_ncard [Finite H] {L : List ℕ} (hnd : L.Nodup) {S : Set H}
    (hL : ∀ N ∈ L, ∃ x ∈ S, R N x) : L.length ≤ S.ncard := by
  classical
  let F : ℕ → H := fun N => if hN : ∃ x, R N x then hN.choose else 1
  have hF : ∀ N x, R N x → F N = x := by
    intro N x hNx
    have hN : ∃ x, R N x := ⟨x, hNx⟩
    simp only [F, dif_pos hN]
    exact (hinj hN.choose_spec hNx).1 rfl
  have hinjF : Set.InjOn F (L.toFinset : Set ℕ) := by
    intro N hN N' hN' e
    rw [Finset.mem_coe, List.mem_toFinset] at hN hN'
    obtain ⟨x, -, hNx⟩ := hL N hN
    obtain ⟨x', -, hNx'⟩ := hL N' hN'
    rw [hF N x hNx, hF N' x' hNx'] at e
    exact (hinj hNx hNx').2 e
  have hsub : ((L.toFinset.image F : Finset H) : Set H) ⊆ S := by
    intro x hx
    rw [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨N, hN, rfl⟩ := hx
    rw [Finset.mem_coe, List.mem_toFinset] at hN
    obtain ⟨x, hx, hNx⟩ := hL N hN
    rw [hF N x hNx]
    exact hx
  have := Set.ncard_le_ncard hsub (Set.toFinite S)
  rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinjF,
    List.toFinset_card_of_nodup hnd] at this

include hinj in
theorem ordB_sound {a p : ℕ} {x : H} (ha : R a x) (h : ordB a p = true) : x ^ p = 1 ∧ x ≠ 1 := by
  unfold ordB at h
  rw [letB_eq', andB_eq', Bool.and_eq_true, notB_eq', Bool.not_eq_true', Nat.beq_eq] at h
  refine ⟨(hinj (powB_sound R hmul hone ha p) hone).1 h.1, fun e => ?_⟩
  have := (hinj ha hone).2 e
  rw [← Nat.beq_eq, h.2] at this
  exact Bool.false_ne_true this

include hinj in
theorem wordsLt_sound {n : ℕ} {tw : List ℕ} {ws : List (List ℕ × ℕ)} (h : wordsLt n tw ws = true) :
    (∀ i ∈ tw, i < n) ∧ ∀ w ∈ ws, ∀ i ∈ w.1, i < n := by
  unfold wordsLt at h
  rw [andB_eq', Bool.and_eq_true] at h
  refine ⟨fun i hi => by
    have := allL_true h.1 i hi
    rwa [Nat.blt_eq] at this, ?_⟩
  have h2 := h.2
  clear h
  induction ws with
  | nil => intro w hw; simp at hw
  | cons w ws ih =>
    change andB (Prod.rec (motive := fun _ => Bool) (fun l _ => allL l fun i => Nat.blt i n) w)
      (List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (Prod.rec
        (motive := fun _ => Bool) (fun l _ => allL l fun i => Nat.blt i n) w) ih) ws) = true at h2
    rw [andB_eq', Bool.and_eq_true] at h2
    intro w' hw' i hi
    rcases List.mem_cons.1 hw' with rfl | hw'
    · obtain ⟨l, e⟩ := w'
      have := allL_true h2.1 i hi
      rwa [Nat.blt_eq] at this
    · exact ih h2.2 w' hw' i hi

include hinj in
theorem invClassK_sound [Finite H] {ls tw : List ℕ} {te : ℕ} {qws : List (List ℕ × ℕ)}
    {qsteps steps : List (ℕ × ℕ)} {i1 i2 : ℕ} {X : ℕ → H} (hX : ∀ i < 4, R (nthV ls i) (X i))
    (h : invClassK ls tw te qws qsteps steps i1 i2 = true) :
    ∃ t ∈ Subgroup.closure {X 0, X 2}, t ^ 2 = 1 ∧ t ≠ 1 ∧
      1 + steps.length ≤ {u | ∃ g ∈ Subgroup.closure {X 0, X 2}, g * t * g⁻¹ = u}.ncard ∧
      (∃ Q : Subgroup H, Q ≤ Subgroup.closure {X 0, X 2} ∧ Q ≤ Subgroup.centralizer {t} ∧
        Nat.card Q = 1 + qsteps.length ∧
        ∀ q ∈ Q, q ^ 2 = 1 → q ≠ 1 → ∃ g ∈ Subgroup.closure {X 0, X 2}, g * t * g⁻¹ = q) ∧
      ∃ g₁ ∈ Subgroup.closure {X 0, X 2}, ∃ g₂ ∈ Subgroup.closure {X 0, X 2},
        orderOf (t * (g₁ * t * g₁⁻¹) * (g₂ * t * g₂⁻¹)) = 7 := by
  set K := Subgroup.closure ({X 0, X 2} : Set H) with hK
  unfold invClassK at h
  rw [andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true, letL_eq, letB_eq', letL_eq] at h
  obtain ⟨-, hwl, h⟩ := h
  obtain ⟨htw, hqw⟩ := wordsLt_sound R hmul hone hinj hwl
  rw [andB_eq', andB_eq', andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hA, hB, ht, hcomm, h⟩ := h
  rw [Nat.beq_eq] at hA hB
  have hA' : X 1 = (X 0)⁻¹ :=
    (eq_inv_of_mul_eq_one_right ((hinj (hmul (hX 0 (by norm_num)) (hX 1 (by norm_num))) hone).1 hA))
  have hB' : X 3 = (X 2)⁻¹ :=
    (eq_inv_of_mul_eq_one_right ((hinj (hmul (hX 2 (by norm_num)) (hX 3 (by norm_num))) hone).1 hB))
  have hXK : ∀ i < 4, X i ∈ K := by
    intro i hi
    have h0 : X 0 ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 : X 2 ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    interval_cases i
    · exact h0
    · rw [hA']; exact K.inv_mem h0
    · exact h2
    · rw [hB']; exact K.inv_mem h2
  have hwK : ∀ w : List ℕ, (∀ i ∈ w, i < 4) → (w.map X).prod ∈ K := by
    intro w hw
    refine K.list_prod_mem fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hXK i (hw i hi)
  set t := (tw.map X).prod ^ te with htdef
  have hRt : R (powB (lineB ls tw) te) t :=
    powB_sound R hmul hone (lineB_sound R hmul hone hX tw htw) te
  have htK : t ∈ K := K.pow_mem (hwK tw htw) te
  obtain ⟨ht2, ht1⟩ := ordB_sound R hmul hone hinj hRt ht
  set g : ℕ → H := fun j => ((qws.getD j ([], 0)).1.map X).prod ^ (qws.getD j ([], 0)).2 with hg
  have hlenW : ∀ ws : List (List ℕ × ℕ), (wordsB ls ws).length = ws.length := by
    intro ws
    induction ws with
    | nil => rfl
    | cons w ws ih => exact congrArg Nat.succ ih
  have hRg : ∀ j < (wordsB ls qws).length, R (nthV (wordsB ls qws) j) (g j) := by
    intro j hj
    rw [hlenW] at hj
    exact wordsB_sound R hmul hone hX qws hqw j hj
  obtain ⟨LQ, -, -, hk, hLQ, hcov, hcard⟩ := subClosK_sound R hmul hone hinj hRg h
  set Q := Subgroup.closure {x | ∃ j < (wordsB ls qws).length, g j = x}
  let P : ℕ → Prop := fun N => ∃ u ∈ K, R N (u * t * u⁻¹)
  have hconj : ∀ {i i' : ℕ}, i < 4 → i' < 4 → X i' = (X i)⁻¹ →
      ∀ N, P N → P (mulB (mulB (nthV ls i) N) (nthV ls i')) := by
    rintro i i' hi hi' e N ⟨u, hu, hN⟩
    refine ⟨X i * u, K.mul_mem (hXK i hi) hu, ?_⟩
    have e' : X i * u * t * (X i * u)⁻¹ = X i * (u * t * u⁻¹) * X i' := by rw [e]; group
    rw [e']
    exact hmul (hmul (hX i hi) hN) (hX i' hi')
  obtain ⟨L, hnd, hlen, -, hPL, hk⟩ := conjOrbThenK_sound P
    ⟨1, K.one_mem, by rw [one_mul, inv_one, mul_one]; exact hRt⟩
    (hconj (by norm_num) (by norm_num) hA') (hconj (by norm_num) (by norm_num) hB') hk
  rw [andB_eq', andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Nat.blt_eq, Nat.blt_eq, lenN_eq_length] at hk
  obtain ⟨hinv, hi1, hi2, h7⟩ := hk
  have hmemL : ∀ {i}, i < L.length → nthV L i ∈ L := by
    intro i hi
    rw [nthV_eq_getD, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  obtain ⟨g₁, hg₁, hR1⟩ := hPL _ (hmemL hi1)
  obtain ⟨g₂, hg₂, hR2⟩ := hPL _ (hmemL hi2)
  obtain ⟨h7a, h7b⟩ := ordB_sound R hmul hone hinj (hmul (hmul hRt hR1) hR2) h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨t, htK, ht2, ht1, ?_, ⟨Q, ?_, ?_, hcard, ?_⟩, g₁, hg₁, g₂, hg₂, orderOf_eq_prime h7a h7b⟩
  · rw [← hlen]
    exact length_le_ncard R hmul hinj hnd fun N hN => by
      obtain ⟨u, hu, hNu⟩ := hPL N hN
      exact ⟨_, ⟨u, hu, rfl⟩, hNu⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [hlenW] at hj
    have hm : qws.getD j ([], 0) ∈ qws := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    exact K.pow_mem (hwK _ fun i hi => hqw _ hm i hi) _
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hgm : nthV (wordsB ls qws) j ∈ wordsB ls qws := by
      rw [nthV_eq_getD, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hc := allL_true hcomm _ hgm
    rw [Nat.beq_eq] at hc
    exact ((hinj (hmul hRt (hRg j hj)) (hmul (hRg j hj) hRt)).1 hc.symm).symm
  · intro q hq hq2 hq1
    obtain ⟨N, hN, hNq⟩ := hcov q hq
    have hNN : mulB N N = oneB := (hinj (hmul hNq hNq) hone).2 (by rw [← pow_two]; exact hq2)
    rcases invInK_sound hinv N hN hNN with e | e
    · exact absurd ((hinj hNq hone).1 e) hq1
    · obtain ⟨u, hu, hNu⟩ := hPL N e
      exact ⟨u, hu, (hinj hNu hNq).1 rfl⟩

end Rel

end CFSG.KC.Misc.E6Std

end
