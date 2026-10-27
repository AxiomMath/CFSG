module

public import Certificates.Kernel.G2Three.Sec1T1Glue2
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1.T1Glue

open Subgroup CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KC.G2Three CFSG.KC.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.KD.G2Three.Sec1.T5Glue CFSG.Open

variable {G : Type} [Group G] [Finite G] (m : G23Model G)

attribute [local irreducible] uE1

theorem cover_of_mono {W : ℕ → ℕ} {n r : ℕ} (hmono : ∀ q, q + 1 < r → W q < W (q + 1))
    (hW : ∀ q < r, W q < n) (bad : Finset ℕ) (hbad : ∀ j ∈ bad, j < n)
    (hdisj : ∀ q < r, W q ∉ bad) (hcard : n ≤ bad.card + r) :
    ∀ j < n, j ∉ bad → ∃ q < r, W q = j := by
  classical
  have hlt : ∀ p q, p < q → q < r → W p < W q := by
    intro p q hpq hq
    induction q with
    | zero => omega
    | succ q ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hpq with h | h
      · exact (ih h (by omega)).trans (hmono q hq)
      · rw [h]
        exact hmono q hq
  have hinj : Set.InjOn W (Finset.range r) := by
    intro p hp q hq hpq
    simp only [Finset.coe_range, Set.mem_Iio] at hp hq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd hpq (hlt p q h hq).ne
    · exact absurd hpq.symm (hlt q p h hp).ne
  set S := (Finset.range r).image W with hSdef
  have hS : S.card = r := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : S ∪ bad ⊆ Finset.range n := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_image] at hj
    rw [Finset.mem_range]
    rcases hj with ⟨q, hq, rfl⟩ | hj
    · exact hW q (Finset.mem_range.mp hq)
    · exact hbad j hj
  have hinter : S ∩ bad = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    obtain ⟨hjS, hjb⟩ := Finset.mem_inter.mp hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hjS
    exact hdisj q (Finset.mem_range.mp hq) hjb
  have hu := Finset.card_union_add_card_inter S bad
  rw [hinter, Finset.card_empty, add_zero, hS] at hu
  have heq : S ∪ bad = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hu, Finset.card_range]; omega)
  intro j hj hjb
  have hjU : j ∈ S ∪ bad := by
    rw [heq]
    exact Finset.mem_range.mpr hj
  rcases Finset.mem_union.mp hjU with h | h
  · obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h
    exact ⟨q, Finset.mem_range.mp hq, e⟩
  · exact absurd h hjb

@[expose] def T0 : Subgroup G := closure {(frameOf m).u₁, (frameOf m).u₂}

theorem T0_le_H : T0 m ≤ g23H m := by
  rw [T0, g23H_eq]
  exact closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

theorem T0_mem {i : ℕ} (hi : i = 7 ∨ i = 0 ∨ i = 8 ∨ i = 2 ∨ i = 18 ∨ i = 32 ∨ i = 33 ∨ i = 19 ∨
    i = 34) : uE1 m i ∈ T0 m := by
  have hu1 : uE1 m 0 ∈ T0 m := by
    rw [uE1_u1]
    exact subset_closure (Set.mem_insert _ _)
  have hu2 : uE1 m 2 ∈ T0 m := by
    rw [uE1_u2]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have h8 : uE1 m 8 ∈ T0 m := by
    rw [← rl' m 0 0 0 8 (by quickRfl)]
    exact mul_mem hu1 hu1
  have h18 : uE1 m 18 ∈ T0 m := by
    rw [← rl' m 10 2 2 18 (by quickRfl)]
    exact mul_mem hu2 hu2
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uE1_seven]
    exact one_mem _
  · exact hu1
  · exact h8
  · exact hu2
  · exact h18
  · rw [← rl' m 24 0 2 32 (by quickRfl)]
    exact mul_mem hu1 hu2
  · rw [← rl' m 25 0 18 33 (by quickRfl)]
    exact mul_mem hu1 h18
  · rw [← rl' m 11 8 2 19 (by quickRfl)]
    exact mul_mem h8 hu2
  · rw [← rl' m 26 8 18 34 (by quickRfl)]
    exact mul_mem h8 h18

@[expose] noncomputable def inT0 (k : ℕ) : Bool :=
  Nat.beq k 7 || Nat.beq k 0 || Nat.beq k 8 || Nat.beq k 2 || Nat.beq k 18 || Nat.beq k 32 ||
    Nat.beq k 33 || Nat.beq k 19 || Nat.beq k 34

theorem T0_mem_of {k : ℕ} (h : inT0 k = true) : uE1 m k ∈ T0 m ∧ k < 37 := by
  simp only [inT0, Bool.or_eq_true, Nat.beq_eq] at h
  refine ⟨T0_mem m (by omega), by omega⟩

@[expose] noncomputable def inZ (e : ℕ) : Bool := Nat.beq e 7 || Nat.beq e 11

theorem uE1_mem_Z_of {e : ℕ} (h : inZ e = true) : uE1 m e ∈ (frameOf m).Z ∧ e < 37 := by
  simp only [inZ, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with rfl | rfl
  · rw [uE1_seven]
    exact ⟨one_mem _, by norm_num⟩
  · rw [uE1_z]
    exact ⟨mem_zpowers _, by norm_num⟩

theorem r1_orbK : (allBelow 6 1 (fun q => inT0 (R1O1K q) && inZ (R1O1E q)) &&
    allBelow 6 1 (fun q => inT0 (R1O2K q) && inZ (R1O2E q)) &&
    allBelow 18 1 (fun q => inT0 (R1O3K q) && inZ (R1O3E q))) = true := by quickRfl

theorem conj_Z {k x : G} (hk : k ∈ g23H m) : x ∈ (frameOf m).Z ↔ k * x * k⁻¹ ∈ (frameOf m).Z := by
  have hc := H_cent_z m k hk
  have hc' : k * (frameOf m).z * k⁻¹ = (frameOf m).z := by rw [hc, mul_inv_cancel_right]
  constructor
  · intro hx
    rcases Z_elem1 m hx with rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [hc']
      exact hx
  · intro hx
    rcases Z_elem1 m hx with h | h
    · have : x = 1 := by
        have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
        rw [e, h]
        group
      rw [this]
      exact one_mem _
    · have : x = (frameOf m).z := by
        have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
        rw [e, h, mul_assoc, ← hc, inv_mul_cancel_left]
      rw [this]
      exact mem_zpowers _

theorem orbit_of_rec {X : Subgroup G} {O : Set G} {T : Subgroup G} {TX K V W E : ℕ → ℕ}
    {n r a : ℕ} (htab : TabOf m.ρ TX n (X : Set G)) (hOX : O ⊆ X) (ha : a < 37) (hr : 0 < r)
    (hK : ∀ q < r, uE1 m (K q) ∈ T ∧ K q < 37) (hE : ∀ q < r, uE1 m (E q) ∈ (frameOf m).Z ∧ E q < 37)
    (h1 : ∀ q < r, MULP (R1U (K q)) (R1U a) = MULP (TX (V q)) (R1U (K q)))
    (h2 : ∀ q < r, MULP (TX (V q)) (R1U 7) = MULP (TX (W q)) (R1U (E q)))
    (hV : ∀ q < r, V q < n) (hW : ∀ q < r, W q < n)
    (hWO : ∀ q < r, ∀ x, Enc m.ρ (TX (W q)) x → x ∈ O)
    (hcover : ∀ j < n, ∀ x, Enc m.ρ (TX j) x → x ∈ O → ∃ q < r, W q = j)
    (hinv : ∀ k ∈ T, ∀ x, x ∈ O ↔ k * x * k⁻¹ ∈ O)
    (hOZ : ∀ x ∈ O, ∀ ζ ∈ (frameOf m).Z, x * ζ ∈ O) :
    IsOrbitMod T (frameOf m).Z O := by
  have key : ∀ q < r, ∃ xW, Enc m.ρ (TX (W q)) xW ∧
      uE1 m (K q) * uE1 m a * (uE1 m (K q))⁻¹ = xW * uE1 m (E q) := by
    intro q hq
    obtain ⟨hKT, hKl⟩ := hK q hq
    obtain ⟨xV, -, hxV⟩ := htab.1 (V q) (hV q hq)
    obtain ⟨xW, -, hxW⟩ := htab.1 (W q) (hW q hq)
    have e1 := mul_eq_of_MULP m.inj (enc_uE1 m hKl) (enc_uE1 m ha) hxV (enc_uE1 m hKl) (h1 q hq)
    have e2 := mul_eq_of_MULP m.inj hxV (enc_uE1 m (by norm_num)) hxW (enc_uE1 m (hE q hq).2)
      (h2 q hq)
    rw [uE1_seven, mul_one] at e2
    refine ⟨xW, hxW, ?_⟩
    rw [e1, mul_inv_cancel_right, e2]
  have huO : uE1 m a ∈ O := by
    obtain ⟨xW, hxW, e⟩ := key 0 hr
    rw [hinv _ (hK 0 hr).1, e]
    exact hOZ _ (hWO 0 hr xW hxW) _ (hE 0 hr).1
  refine ⟨uE1 m a, huO, Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · obtain ⟨j, hj, hwj⟩ := htab.2 w (hOX hw)
    obtain ⟨q, hq, rfl⟩ := hcover j hj w hwj hw
    obtain ⟨xW, hxW, e⟩ := key q hq
    have hxw : xW = w := enc_unique m.inj hxW hwj
    refine ⟨uE1 m (K q), (hK q hq).1, ?_⟩
    rw [e, hxw, mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem (hE q hq).1
  · obtain ⟨k, hk, hζ⟩ := hw
    have e : w = k * uE1 m a * k⁻¹ * ((k * uE1 m a * k⁻¹)⁻¹ * w) := by group
    rw [e]
    exact hOZ _ ((hinv k hk _).mp huO) _ hζ

theorem mono_of {W : ℕ → ℕ} {r : ℕ} (h : allBelow r 1 (fun q => Nat.blt (W q) (W (Nat.succ q))) = true)
    (hr : r ≤ 64) : ∀ q, q + 1 < r + 1 → W q < W (q + 1) := fun q hq =>
  Nat.blt_eq.mp (allBelow_g2 h (by omega) q (by omega))

theorem Z_le_of {X : Subgroup G} (hz : (frameOf m).z ∈ X) : (frameOf m).Z ≤ X := by
  rw [SFrame.Z, zpowers_le]
  exact hz

theorem inv_diffZ {X : Subgroup G} (hHX : g23H m ≤ normalizer (X : Set G)) {k : G}
    (hk : k ∈ g23H m) (x : G) :
    x ∈ (X : Set G) \ ((frameOf m).Z : Set G) ↔
      k * x * k⁻¹ ∈ (X : Set G) \ ((frameOf m).Z : Set G) := by
  have hn := mem_normalizer_iff.mp (hHX hk) x
  simp only [Set.mem_diff, SetLike.mem_coe]
  rw [← hn, ← conj_Z m hk]

theorem orbit_Q {X : Subgroup G} {TX K V W E : ℕ → ℕ} {a : ℕ}
    (htab : TabOf m.ρ TX 8 (X : Set G)) (h0 : TX 0 = ONEP) (hzX : (frameOf m).z ∈ X)
    (hHX : g23H m ≤ normalizer (X : Set G)) (ha : a < 37)
    (hrec : (eqK (fun q => R1U (K q)) (fun _ => R1U a) (fun q => TX (V q)) (fun q => R1U (K q)) 6 1 &&
      eqK (fun q => TX (V q)) (fun _ => R1U 7) (fun q => TX (W q)) (fun q => R1U (E q)) 6 1 &&
      ltK V 8 6 1 && ltK W 8 6 1 && allBelow 5 1 (fun q => Nat.blt (W q) (W (Nat.succ q))) &&
      neK (fun q => TX (W (Nat.div q 2))) (fun _ => R1U 7)
        (fun q => R1U (Nat.add 7 (Nat.mul 4 (Nat.mod q 2)))) (fun _ => R1U 7) 12 1) = true)
    (hKE : allBelow 6 1 (fun q => inT0 (K q) && inZ (E q)) = true) :
    IsOrbitMod (T0 m) (frameOf m).Z ((X : Set G) \ ((frameOf m).Z : Set G)) := by
  classical
  simp only [Bool.and_eq_true] at hrec
  obtain ⟨⟨⟨⟨⟨e1, e2⟩, lV⟩, lW⟩, mono⟩, ne⟩ := hrec
  have hKE' : ∀ q < 6, inT0 (K q) = true ∧ inZ (E q) = true := fun q hq => by
    have := allBelow_g2 hKE (by norm_num) q hq
    simpa only [Bool.and_eq_true] using this
  have hZX := Z_le_of m hzX
  have hn : ∀ q < 6, MULP (TX (W q)) (R1U 7) ≠ MULP (R1U 7) (R1U 7) ∧
      MULP (TX (W q)) (R1U 7) ≠ MULP (R1U 11) (R1U 7) := by
    intro q hq
    have n0 := neK_at ne (by norm_num) (2 * q) (by omega)
    have n1 := neK_at ne (by norm_num) (2 * q + 1) (by omega)
    have d0 : Nat.div (2 * q) 2 = q := by
      change 2 * q / 2 = q
      omega
    have d1 : Nat.div (2 * q + 1) 2 = q := by
      change (2 * q + 1) / 2 = q
      omega
    have m0 : Nat.add 7 (Nat.mul 4 (Nat.mod (2 * q) 2)) = 7 := by
      change 7 + 4 * (2 * q % 2) = 7
      omega
    have m1 : Nat.add 7 (Nat.mul 4 (Nat.mod (2 * q + 1) 2)) = 11 := by
      change 7 + 4 * ((2 * q + 1) % 2) = 11
      omega
    beta_reduce at n0 n1
    rw [d0, m0] at n0
    rw [d1, m1] at n1
    exact ⟨n0, n1⟩
  have hWnZ : ∀ q < 6, ∀ x, Enc m.ρ (TX (W q)) x → x ∉ (frameOf m).Z := by
    intro q hq x hx hxZ
    have h7 := enc_uE1 m (i := 7) (by norm_num)
    have h11 := enc_uE1 m (i := 11) (by norm_num)
    rw [uE1_seven] at h7
    rw [uE1_z] at h11
    rcases Z_elem1 m hxZ with rfl | rfl
    · exact mul_ne_of_MULP hx h7 h7 h7 (hn q hq).1 rfl
    · exact mul_ne_of_MULP hx h7 h11 h7 (hn q hq).2 rfl
  obtain ⟨iz, hiz, hizE⟩ := htab.2 _ hzX
  have henc0 : Enc m.ρ (TX 0) 1 := by
    rw [h0]
    exact enc_one m.ρ
  have hiz0 : iz ≠ 0 := by
    rintro rfl
    exact z_ne_one m (enc_unique m.inj hizE henc0)
  have hcover := cover_of_mono (mono_of mono (by norm_num)) (ltK_at lW (by norm_num)) {0, iz}
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · norm_num
      · exact hiz)
    (by
      intro q hq hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      obtain ⟨x, -, hx⟩ := htab.1 (W q) (ltK_at lW (by norm_num) q hq)
      rcases hb with hb | hb
      · rw [hb] at hx
        exact hWnZ q hq x (by rw [hb]; exact hx) (by rw [enc_unique m.inj hx henc0]; exact one_mem _)
      · rw [hb] at hx
        exact hWnZ q hq x (by rw [hb]; exact hx) (by rw [enc_unique m.inj hx hizE]; exact mem_zpowers _))
    (by rw [Finset.card_pair hiz0.symm])
  refine orbit_of_rec m htab Set.diff_subset ha (by norm_num) (fun q hq => T0_mem_of m (hKE' q hq).1)
    (fun q hq => uE1_mem_Z_of m (hKE' q hq).2) (fun q hq => eqK_at e1 (by norm_num) q hq)
    (fun q hq => eqK_at e2 (by norm_num) q hq) (ltK_at lV (by norm_num)) (ltK_at lW (by norm_num))
    ?_ ?_ (fun k hk x => inv_diffZ m hHX (T0_le_H m hk) x) ?_
  · intro q hq x hx
    obtain ⟨y, hyX, hy⟩ := htab.1 (W q) (ltK_at lW (by norm_num) q hq)
    rw [enc_unique m.inj hx hy]
    exact ⟨hyX, hWnZ q hq y hy⟩
  · intro j hj x hx hxO
    refine hcover j hj ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hxO.2 (by rw [enc_unique m.inj hx henc0]; exact one_mem _)
    · exact hxO.2 (by rw [enc_unique m.inj hx hizE]; exact mem_zpowers _)
  · intro x hx ζ hζ
    refine ⟨hZX ?_ |> fun h => mul_mem hx.1 h, fun hxζ => hx.2 ?_⟩
    · exact hζ
    · have e : x = x * ζ * ζ⁻¹ := by group
      rw [e]
      exact mul_mem hxζ (inv_mem hζ)

theorem z_mem_Q1 : (frameOf m).z ∈ closure {(frameOf m).a₁, (frameOf m).b₁} := by
  rw [SFrame.z, pow_two]
  exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem z_mem_Q2 : (frameOf m).z ∈ closure {(frameOf m).a₂, (frameOf m).b₂} := by
  have h := sw m 5 11 11 (by quickRfl)
  rw [uE1_z] at h
  have hb : (frameOf m).b₂ = (frameOf m).σ * (frameOf m).b₁ * (frameOf m).σ⁻¹ := by
    have h' := sw m 2 1 3 (by quickRfl)
    rw [uE1_b1, uE1_b2] at h'
    exact h'.symm
  rw [← h, SFrame.z, pow_two]
  have e : (frameOf m).σ * ((frameOf m).b₁ * (frameOf m).b₁) * (frameOf m).σ⁻¹ =
      (frameOf m).b₂ * (frameOf m).b₂ := by
    rw [hb]
    group
  rw [e]
  exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem orbit1 : IsOrbitMod (T0 m) (frameOf m).Z
    ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) \ ((frameOf m).Z : Set G)) := by
  have hrK := r1_orbK
  simp only [Bool.and_eq_true] at hrK
  have htab := (tabQ1 m).1
  rw [Q1_eq] at htab
  exact orbit_Q m htab r1_ones.2.2.2.2.1 (z_mem_Q1 m) (H_norm_Q1 m) (by norm_num) r1_orb1 hrK.1.1

theorem orbit2 : IsOrbitMod (T0 m) (frameOf m).Z
    ((closure {(frameOf m).a₂, (frameOf m).b₂} : Set G) \ ((frameOf m).Z : Set G)) := by
  have hrK := r1_orbK
  simp only [Bool.and_eq_true] at hrK
  have htab := (tabQ2 m).1
  rw [Q2_eq] at htab
  exact orbit_Q m htab r1_ones.2.2.2.2.2.1 (z_mem_Q2 m) (H_norm_Q2 m) (by norm_num) r1_orb2 hrK.1.2

theorem injOn_idx {ι TQ TA : ℕ → ℕ} {n : ℕ} (hinj : ∀ i < n, ∀ j < n, TQ i = TQ j → i = j)
    (h : ∀ i < n, ∃ x : G, Enc m.ρ (TQ i) x ∧ Enc m.ρ (TA (ι i)) x) :
    Set.InjOn ι (Finset.range n) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  obtain ⟨x, hx, hxA⟩ := h i hi
  obtain ⟨y, hy, hyA⟩ := h j hj
  rw [hij] at hxA
  have e := enc_unique m.inj hxA hyA
  rw [e] at hx
  exact hinj i hi j hj (enc_inj hx hy)

theorem inv_O3 {k : G} (hk : k ∈ g23H m) (x : G) :
    x ∈ ((frameOf m).A : Set G) \ ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
      (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G)) ↔
    k * x * k⁻¹ ∈ ((frameOf m).A : Set G) \ ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
      (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G)) := by
  have hA := mem_normalizer_iff.mp (H_norm_A m hk) x
  have h1 := mem_normalizer_iff.mp (H_norm_Q1 m hk) x
  have h2 := mem_normalizer_iff.mp (H_norm_Q2 m hk) x
  simp only [Set.mem_diff, Set.mem_union, SetLike.mem_coe]
  rw [← hA, ← h1, ← h2]

theorem Q1_le_A : closure {(frameOf m).a₁, (frameOf m).b₁} ≤ (frameOf m).A := by
  rw [SFrame.A]
  exact closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

theorem Q2_le_A : closure {(frameOf m).a₂, (frameOf m).b₂} ≤ (frameOf m).A := by
  rw [SFrame.A]
  exact closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

theorem orbit3 : IsOrbitMod (T0 m) (frameOf m).Z (((frameOf m).A : Set G) \
    ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
      (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G))) := by
  classical
  have hrK := r1_orbK
  simp only [Bool.and_eq_true] at hrK
  have hKE' : ∀ q < 18, inT0 (R1O3K q) = true ∧ inZ (R1O3E q) = true := fun q hq => by
    have := allBelow_g2 hrK.2 (by norm_num) q hq
    simpa only [Bool.and_eq_true] using this
  have hrec := r1_orb3
  simp only [Bool.and_eq_true] at hrec
  obtain ⟨⟨⟨⟨⟨⟨e1, e2⟩, lV⟩, lW⟩, mono⟩, ne1⟩, ne2⟩ := hrec
  have htA := tabA' m
  have hinjA := (tabA m).2.2
  have htQ1 := (tabQ1 m).1
  rw [Q1_eq] at htQ1
  have htQ2 := (tabQ2 m).1
  rw [Q2_eq] at htQ2
  have h7 := enc_uE1 m (i := 7) (by norm_num)
  rw [uE1_seven] at h7
  have hnQ : ∀ q < 18, ∀ x, Enc m.ρ (R1A (R1O3W q)) x →
      x ∉ closure {(frameOf m).a₁, (frameOf m).b₁} ∧ x ∉ closure {(frameOf m).a₂, (frameOf m).b₂} := by
    intro q hq x hx
    have d : ∀ i < 8, Nat.div (8 * q + i) 8 = q ∧ Nat.mod (8 * q + i) 8 = i := fun i hi => by
      constructor
      · change (8 * q + i) / 8 = q
        omega
      · change (8 * q + i) % 8 = i
        omega
    constructor
    · intro hxQ
      obtain ⟨i, hi, hyi⟩ := htQ1.2 x hxQ
      have n := neK_at ne1 (by norm_num) (8 * q + i) (by omega)
      beta_reduce at n
      rw [(d i hi).1, (d i hi).2] at n
      exact mul_ne_of_MULP hx h7 hyi h7 n rfl
    · intro hxQ
      obtain ⟨i, hi, hyi⟩ := htQ2.2 x hxQ
      have n := neK_at ne2 (by norm_num) (8 * q + i) (by omega)
      beta_reduce at n
      rw [(d i hi).1, (d i hi).2] at n
      exact mul_ne_of_MULP hx h7 hyi h7 n rfl
  have hι1 : ∀ i, ∃ j, i < 8 → j < 32 ∧ ∃ x, Enc m.ρ (R1Q1 i) x ∧ Enc m.ρ (R1A j) x ∧
      x ∈ closure {(frameOf m).a₁, (frameOf m).b₁} := by
    intro i
    by_cases hi : i < 8
    · obtain ⟨x, hxQ, hx⟩ := htQ1.1 i hi
      obtain ⟨j, hj, hxj⟩ := htA.2 x (Q1_le_A m hxQ)
      exact ⟨j, fun _ => ⟨hj, x, hx, hxj, hxQ⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  have hι2 : ∀ i, ∃ j, i < 8 → j < 32 ∧ ∃ x, Enc m.ρ (R1Q2 i) x ∧ Enc m.ρ (R1A j) x ∧
      x ∈ closure {(frameOf m).a₂, (frameOf m).b₂} := by
    intro i
    by_cases hi : i < 8
    · obtain ⟨x, hxQ, hx⟩ := htQ2.1 i hi
      obtain ⟨j, hj, hxj⟩ := htA.2 x (Q2_le_A m hxQ)
      exact ⟨j, fun _ => ⟨hj, x, hx, hxj, hxQ⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose ι1 hι1 using hι1
  choose ι2 hι2 using hι2
  have hinj1 := injOn_idx m (ι := ι1) (TA := R1A) (tabQ1 m).2.2 (fun i hi => by
    obtain ⟨-, x, hx, hxA, -⟩ := hι1 i hi
    exact ⟨x, hx, hxA⟩)
  have hinj2 := injOn_idx m (ι := ι2) (TA := R1A) (tabQ2 m).2.2 (fun i hi => by
    obtain ⟨-, x, hx, hxA, -⟩ := hι2 i hi
    exact ⟨x, hx, hxA⟩)
  set I1 := (Finset.range 8).image ι1 with hI1
  set I2 := (Finset.range 8).image ι2 with hI2
  have hc1 : I1.card = 8 := by rw [hI1, Finset.card_image_of_injOn hinj1, Finset.card_range]
  have hc2 : I2.card = 8 := by rw [hI2, Finset.card_image_of_injOn hinj2, Finset.card_range]
  obtain ⟨izA, hizA, hizAE⟩ := htA.2 _ (z_mem_A m)
  have henc0 : Enc m.ρ (R1A 0) 1 := by
    rw [r1_ones.2.2.2.2.2.2.2.1]
    exact enc_one m.ρ
  have hinter : I1 ∩ I2 ⊆ {0, izA} := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_inter.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj1
    obtain ⟨i', hi', e⟩ := Finset.mem_image.mp hj2
    obtain ⟨hjl, x, -, hxA, hxQ⟩ := hι1 i (Finset.mem_range.mp hi)
    obtain ⟨-, y, -, hyA, hyQ⟩ := hι2 i' (Finset.mem_range.mp hi')
    rw [← e] at hxA
    have hxy := enc_unique m.inj hxA hyA
    have hxZ : x ∈ (frameOf m).Z := by
      rw [← K_inter m]
      exact ⟨Q1_le_K1 m hxQ, Q2_le_K2 m (hxy ▸ hyQ)⟩
    rw [← e] at hjl
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases Z_elem1 m hxZ with rfl | rfl
    · rw [← e]
      exact Or.inl (hinjA _ hjl 0 (by norm_num) (enc_inj hyA (hxy ▸ henc0)))
    · rw [← e]
      exact Or.inr (hinjA _ hjl izA hizA (enc_inj hyA (hxy ▸ hizAE)))
  have hcardI : 14 ≤ (I1 ∪ I2).card := by
    have hu := Finset.card_union_add_card_inter I1 I2
    have hle : (I1 ∩ I2).card ≤ 2 :=
      (Finset.card_le_card hinter).trans ((Finset.card_insert_le _ _).trans (by simp))
    omega
  have hnotI : ∀ j ∈ I1 ∪ I2, ∀ x, Enc m.ρ (R1A j) x →
      x ∈ closure {(frameOf m).a₁, (frameOf m).b₁} ∨ x ∈ closure {(frameOf m).a₂, (frameOf m).b₂} := by
    intro j hj x hx
    rcases Finset.mem_union.mp hj with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨-, y, -, hyA, hyQ⟩ := hι1 i (Finset.mem_range.mp hi)
      rw [enc_unique m.inj hx hyA]
      exact Or.inl hyQ
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨-, y, -, hyA, hyQ⟩ := hι2 i (Finset.mem_range.mp hi)
      rw [enc_unique m.inj hx hyA]
      exact Or.inr hyQ
  have hcover := cover_of_mono (mono_of mono (by norm_num)) (ltK_at lW (by norm_num)) (I1 ∪ I2)
    (by
      intro j hj
      rcases Finset.mem_union.mp hj with h | h
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact (hι1 i (Finset.mem_range.mp hi)).1
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact (hι2 i (Finset.mem_range.mp hi)).1)
    (by
      intro q hq hb
      obtain ⟨x, -, hx⟩ := htA.1 (R1O3W q) (ltK_at lW (by norm_num) q hq)
      rcases hnotI _ hb x hx with h | h
      · exact (hnQ q hq x hx).1 h
      · exact (hnQ q hq x hx).2 h)
    (by omega)
  have hZA := Z_le_of m (z_mem_A m)
  have hZ1 := Z_le_of m (z_mem_Q1 m)
  have hZ2 := Z_le_of m (z_mem_Q2 m)
  refine orbit_of_rec m htA Set.diff_subset (by norm_num) (by norm_num)
    (fun q hq => T0_mem_of m (hKE' q hq).1) (fun q hq => uE1_mem_Z_of m (hKE' q hq).2)
    (fun q hq => eqK_at e1 (by norm_num) q hq) (fun q hq => eqK_at e2 (by norm_num) q hq)
    (ltK_at lV (by norm_num)) (ltK_at lW (by norm_num)) ?_ ?_
    (fun k hk x => inv_O3 m (T0_le_H m hk) x) ?_
  · intro q hq x hx
    obtain ⟨y, hyA, hy⟩ := htA.1 (R1O3W q) (ltK_at lW (by norm_num) q hq)
    rw [enc_unique m.inj hx hy]
    refine ⟨hyA, ?_⟩
    rintro (h | h)
    · exact (hnQ q hq y hy).1 h
    · exact (hnQ q hq y hy).2 h
  · intro j hj x hx hxO
    refine hcover j hj fun hb => ?_
    rcases hnotI j hb x hx with h | h
    · exact hxO.2 (Or.inl h)
    · exact hxO.2 (Or.inr h)
  · intro x hx ζ hζ
    refine ⟨mul_mem hx.1 (hZA hζ), ?_⟩
    have e : x = x * ζ * ζ⁻¹ := by group
    rintro (h | h)
    · exact hx.2 (Or.inl (by rw [e]; exact mul_mem h (inv_mem (hZ1 hζ))))
    · exact hx.2 (Or.inr (by rw [e]; exact mul_mem h (inv_mem (hZ2 hζ))))

theorem cube_closure_pair {a b : G} (hc : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    ∀ x ∈ closure ({a, b} : Set G), x ^ 3 = 1 := by
  have hc1 : ∀ x ∈ closure ({a, b} : Set G), Commute x a ∧ Commute x b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨Commute.refl _, hc⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨hc.symm, Commute.refl _⟩
    | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
    | mul x y _ _ ihx ihy => exact ⟨ihx.1.mul_left ihy.1, ihx.2.mul_left ihy.2⟩
    | inv x _ ih => exact ⟨ih.1.inv_left, ih.2.inv_left⟩
  have hcomm : ∀ x ∈ closure ({a, b} : Set G), ∀ y ∈ closure ({a, b} : Set G), Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact (hc1 x hx).1
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hc1 x hx).2
    | one => exact Commute.one_right _
    | mul y z _ _ ihy ihz => exact ihy.mul_right ihz
    | inv y _ ih => exact ih.inv_right
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hb
  | one => exact one_pow _
  | mul x y hx hy ihx ihy => rw [(hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

theorem pU_pow_inj : ∀ p q : Fin 3 × Fin 3,
    pU 0 ^ (p.1 : ℕ) * pU 2 ^ (p.2 : ℕ) = pU 0 ^ (q.1 : ℕ) * pU 2 ^ (q.2 : ℕ) → p = q := by
  decide

theorem T0_pgroup : IsPGroup 3 (T0 m) := by
  have hc : Commute (frameOf m).u₁ (frameOf m).u₂ :=
    K_comm m _ (by rw [SFrame.K₁]; exact subset_closure (by simp)) _
      (by rw [SFrame.K₂]; exact subset_closure (by simp))
  have h1 : (frameOf m).u₁ ^ 3 = 1 := by
    rw [← u1_order m]
    exact pow_orderOf_eq_one _
  have h2 : (frameOf m).u₂ ^ 3 = 1 := by
    rw [← u2_order m]
    exact pow_orderOf_eq_one _
  have hcube := cube_closure_pair hc h1 h2
  exact fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hcube _ g.2)⟩

theorem T0_card : 9 ≤ Nat.card (T0 m) := by
  obtain ⟨φ, -, -, hU⟩ := T1_hom m
  have hT0T1 : T0 m ≤ g23T1 m := (T0_le_H m).trans (H_le_T1 m)
  have hu1 : uE1 m 0 ∈ T0 m := T0_mem m (by decide)
  have hu2 : uE1 m 2 ∈ T0 m := T0_mem m (by decide)
  let f : Fin 3 × Fin 3 → T0 m := fun p =>
    ⟨uE1 m 0 ^ (p.1 : ℕ) * uE1 m 2 ^ (p.2 : ℕ), mul_mem (pow_mem hu1 _) (pow_mem hu2 _)⟩
  have hφf : ∀ p : Fin 3 × Fin 3, φ ⟨f p, hT0T1 (f p).2⟩ = pU 0 ^ (p.1 : ℕ) * pU 2 ^ (p.2 : ℕ) := by
    intro p
    have e : (⟨(f p : G), hT0T1 (f p).2⟩ : ↥(g23T1 m)) =
        (⟨uE1 m 0, H_le_T1 m (uE1_mem m 0)⟩ : ↥(g23T1 m)) ^ (p.1 : ℕ) *
          (⟨uE1 m 2, H_le_T1 m (uE1_mem m 2)⟩ : ↥(g23T1 m)) ^ (p.2 : ℕ) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    rw [e, map_mul, map_pow, map_pow, hU 0 (by norm_num), hU 2 (by norm_num)]
  have hinj : Function.Injective f := fun p q hpq => pU_pow_inj p q (by
    have := congrArg (fun x : T0 m => φ ⟨x, hT0T1 x.2⟩) hpq
    rwa [hφf, hφf] at this)
  have := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_prod, Nat.card_fin] at this

theorem T0_sylow : IsSylowIn 3 (g23H m) (T0 m) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp := T0_pgroup m
  have h9 := T0_card m
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  have hrel := relIndex_mul_card (H := T0 m) (K := g23H m)
  rw [inf_of_le_left (T0_le_H m), hn, card_H] at hrel
  rw [hn] at h9
  have hd : 3 ^ n ∣ 576 := ⟨(T0 m).relIndex (g23H m), by rw [← hrel, mul_comm]⟩
  have hle : n ≤ 2 := by
    by_contra h
    have h3 := (Nat.pow_dvd_pow 3 (show 3 ≤ n by omega)).trans hd
    norm_num at h3
  refine ⟨T0_le_H m, hp, ?_⟩
  interval_cases n
  · norm_num at h9
  · norm_num at h9
  · have h64 : (T0 m).relIndex (g23H m) = 64 := by omega
    rw [h64]
    norm_num

theorem H_norm_Z {g : G} (hg : g ∈ g23H m) : g ∈ normalizer ((frameOf m).Z : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  exact conj_Z m hg

theorem A_orbits : ∀ T : Subgroup G, IsSylowIn 3 (g23H m) T →
    IsOrbitMod T (frameOf m).Z
      ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) \ ((frameOf m).Z : Set G)) ∧
    IsOrbitMod T (frameOf m).Z
      ((closure {(frameOf m).a₂, (frameOf m).b₂} : Set G) \ ((frameOf m).Z : Set G)) ∧
    IsOrbitMod T (frameOf m).Z ((frameOf m).A \
      ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
        (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact forall_isSylowIn_of_one (T0_sylow m) ⟨orbit1 m, orbit2 m, orbit3 m⟩ fun g hg _ =>
    ⟨isOrbitMod_conj (H_norm_Z m hg) (inv_diffZ m (H_norm_Q1 m) hg) (orbit1 m),
      isOrbitMod_conj (H_norm_Z m hg) (inv_diffZ m (H_norm_Q2 m) hg) (orbit2 m),
      isOrbitMod_conj (H_norm_Z m hg) (inv_O3 m hg) (orbit3 m)⟩

theorem facts : G23T1Facts m where
  z_order := z_order m
  card_H := card_H m
  H_cent_z := H_cent_z m
  centIn_H_F := centIn_H_F m
  K1_iso := K1_iso m
  K2_iso := K2_iso m
  K1_normal := K1_normal m
  K2_normal := K2_normal m
  K_comm := K_comm m
  K_inter := K_inter m
  pCore1 := pCore1 m
  pCore2 := pCore2 m
  X1_sylow := X1_sylow m
  X2_sylow := X2_sylow m
  h0_inv1 := h0_inv1 m
  h0_inv2 := h0_inv2 m
  sigma_K1 := sigma_K1 m
  F_cent_sigma := F_cent_sigma m
  cen_S := cen_S m
  cen_A := cen_A m
  normIn_H_A := normIn_H_A m
  normIn_H_S := normIn_H_S m
  normIn_H_B := normIn_H_B m
  A_frob := A_frob m
  A_orbits := A_orbits m
  centIn_H_cen_B := centIn_H_cen_B m
  card_E := card_E m
  elemAb_E := elemAb_E m
  centIn_H_E := centIn_H_E m
  card_normIn_H_E := card_normIn_H_E m
  fix_E := fix_E m
  E_S3 := E_S3 m
  E_trans := E_trans m
  E_sylow := E_sylow m
  Y2_conj := Y2_conj m
  Y3_conj := Y3_conj m
  card_T1 := card_T1 m
  T1_le_cent := T1_le_cent m
  T1_S3S3 := T1_S3S3 m
  commMod_A := commMod_A m
  commMod_EF := commMod_EF m

end CFSG.KD.G2Three.Sec1.T1Glue

end
