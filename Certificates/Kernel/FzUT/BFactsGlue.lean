module

public import Certificates.Kernel.FzUT.BModEq
public import Certificates.Kernel.FzUT.BFacts

public section

namespace CFSG.KC.FzBMod

open Certificates.FzBU CFSG.OddStandard.SmallF3.FritzII

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : Bool.rec (motive := fun _ => Nat) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem letN_eq (y : Nat) (k : Nat → Bool) : letN y k = k y := by
  cases y <;> rfl

theorem allL_iff (L : List Nat) (f : Nat → Bool) : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx (List.not_mem_nil), fun _ => rfl⟩
  | cons a L ih =>
    change Bool.rec (motive := fun _ => Bool) false (allL L f) (f a) = true ↔ _
    rw [bIf_eq]
    cases h : f a <;> simp [h, ih]

theorem anyL_iff (L : List Nat) (f : Nat → Bool) : anyL L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => exact ⟨fun h => absurd h (by simp [anyL]), fun ⟨x, hx, _⟩ => absurd hx (List.not_mem_nil)⟩
  | cons a L ih =>
    change Bool.rec (motive := fun _ => Bool) (anyL L f) true (f a) = true ↔ _
    rw [bIf_eq]
    cases h : f a <;> simp [h, ih]

theorem memL_iff (v : Nat) (L : List Nat) : memL v L = true ↔ v ∈ L := by
  unfold memL
  rw [anyL_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← Nat.eq_of_beq_eq_true h]
  · intro h
    exact ⟨v, h, Nat.beq_refl v⟩

theorem mulN_split (c : Bool) (x y : Nat) :
    ∃ u < 64, mulN c x y = u + 64 * amulL (x / 64) (y / 64) := by
  have e1 : ∀ z : Nat, Nat.land z 63 < 64 := fun z => Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have e2 : ∀ z : Nat, Nat.shiftRight z 6 = z / 64 := fun z => by
    have h := Nat.shiftRight_eq_div_pow z 6
    norm_num at h
    exact h
  have e3 : ∀ z : Nat, Nat.shiftLeft z 6 = 64 * z := fun z => by
    have h := Nat.shiftLeft_eq z 6
    norm_num at h
    rw [Nat.mul_comm]
    exact h
  refine ⟨uMulP (Nat.land x 63) (actL c (Nat.shiftRight x 6) (Nat.land y 63)), ?_, ?_⟩
  · rw [uMulP_eq (e1 x) (actL_lt _ _ _)]
    exact fzb_uMul_lt (e1 x) (actL_lt _ _ _)
  · change Nat.add _ (Nat.shiftLeft _ 6) = _
    rw [e3, e2, e2, Nat.add_eq]

theorem amulL_lt (w v : Nat) : amulL w v < 16 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem mulN_lt (c : Bool) (x y : Nat) : mulN c x y < 1024 := by
  obtain ⟨u, hu, h⟩ := mulN_split c x y
  have := amulL_lt (x / 64) (y / 64)
  omega

theorem mulN_div (c : Bool) (x y : Nat) : mulN c x y / 64 = amulL (x / 64) (y / 64) := by
  obtain ⟨u, hu, h⟩ := mulN_split c x y
  omega

theorem fzbW0_iff (x : Nat) : fzbW0 x ↔ ∃ i < 8, w0E i = x := by
  have hE : ∀ i, w0E i = if i < 4 then i else i + 124 := fun i => by
    unfold w0E
    rw [nIf_eq]
    simp only [Nat.blt_eq, Nat.add_eq]
  unfold fzbW0
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact ⟨x, by omega, by rw [hE, if_pos h]⟩
    · exact ⟨x - 124, by omega, by rw [hE, if_neg (by omega)]; omega⟩
  · rintro ⟨i, hi, rfl⟩
    rw [hE]
    split_ifs with h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩

theorem w0N_iff (x : Nat) : w0N x = true ↔ fzbW0 x := by
  unfold w0N fzbW0
  rw [bIf_eq, bIf_eq]
  by_cases h1 : x < 4
  · rw [if_pos (by simp [Nat.blt_eq, h1])]
    exact ⟨fun _ => Or.inl h1, fun _ => rfl⟩
  · rw [if_neg (by simp [Nat.blt_eq, h1])]
    by_cases h2 : 128 ≤ x
    · rw [if_pos (by simp [Nat.ble_eq, h2]), Nat.blt_eq]
      constructor
      · intro h
        exact Or.inr ⟨h2, h⟩
      · rintro (h | ⟨-, h⟩)
        · omega
        · exact h
    · rw [if_neg (by simp [Nat.ble_eq, h2])]
      constructor
      · intro h
        exact absurd h (by simp)
      · rintro (h | ⟨h, -⟩) <;> omega

theorem fzbFactsGen_mk (c : Bool) : FzbFactsGen c := by
  have hs := ch441796_small c
  simp only [smallB, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩ := hs
  have E : ∀ {x y : Nat}, x < 1024 → y < 1024 → fzbMul c x y = mulN c x y :=
    fun hx hy => fzbMul_eq c hx hy
  have B := @Nat.eq_of_beq_eq_true
  have e128_1 : fzbMul c 128 1 = 129 := by rw [E (by norm_num) (by norm_num)]; exact B h5
  have e832_1 : fzbMul c 832 1 = 833 := by rw [E (by norm_num) (by norm_num)]; exact B h7
  have e128_832 : fzbMul c 128 832 = 960 := by rw [E (by norm_num) (by norm_num)]; exact B h8
  have e960_1 : fzbMul c 960 1 = 961 := by rw [E (by norm_num) (by norm_num)]; exact B h10
  refine
    { mul_lt := fun x hx y hy => by rw [E hx hy]; exact mulN_lt c x y
      t_eq := by rw [E (by norm_num) (by norm_num)]; exact B h1
      qs_eq := by rw [E (by norm_num) (by norm_num)]; exact B h2
      qsy_eq := by rw [E (by norm_num) (by norm_num)]; exact B h3
      card_M := ?_
      M_mul := ?_
      M_sq := ?_
      F3 := ?_
      V2 := ?_
      W0_mul := ?_
      comm_z_t := by rw [e128_1, E (by norm_num) (by norm_num)]; exact B h4
      comm_z_u := by rw [e832_1, E (by norm_num) (by norm_num)]; exact B h6
      comm_t_u := by
        rw [e128_832, E (by norm_num) (by norm_num)]
        exact (B h9).symm
      sq_z := by rw [E (by norm_num) (by norm_num)]; exact B h11
      sq_t := by rw [E (by norm_num) (by norm_num)]; exact B h12
      sq_u := by rw [E (by norm_num) (by norm_num)]; exact B h13
      nodup := by rw [e128_1, e832_1, e128_832, e960_1]; simp
      conj_tz := ⟨4, by norm_num, by
        rw [e128_1, E (by norm_num) (by norm_num), E (by norm_num) (by norm_num)]; exact B h14⟩
      conj_uz := ⟨2, by norm_num, by
        rw [e832_1, E (by norm_num) (by norm_num), E (by norm_num) (by norm_num)]; exact B h15⟩
      conj_tu := ⟨64, by norm_num, by
        rw [e128_832, E (by norm_num) (by norm_num), E (by norm_num) (by norm_num)]
        exact B h16⟩
      conj_tuz := ⟨66, by norm_num, by
        rw [e128_832, e960_1, E (by norm_num) (by norm_num), E (by norm_num) (by norm_num)]
        exact B h17⟩ }
  · have h := B ch441796_cardM
    rw [countN_eq] at h
    rw [← h]
    congr 1
    try (refine Finset.filter_congr (fun x _ => ?_); simp [fzbIsM, Nat.beq_eq])
  · intro x hx hxM y hy hyM
    unfold fzbIsM at hxM hyM ⊢
    rw [E hx hy, mulN_div]
    have h := (allN_iff 16 _).mp ((allN_iff 16 _).mp ch441796_mmul (x / 64) (by omega)) (y / 64)
      (by omega)
    simp only [bIf_eq, Nat.beq_eq, hxM, hyM, if_true] at h
    exact h
  · intro m hm hmM
    unfold fzbIsM at hmM
    rw [E hm hm]
    have h := (allN_iff 16 _).mp ch441796_msq (m / 64) (by omega)
    simp only [bIf_eq, Nat.beq_eq, hmM, if_true] at h
    obtain ⟨u, hu, hsplit⟩ := mulN_split c m m
    rw [hsplit, h]
    omega
  · intro z hz0 hz4
    have key : ∀ z < 4, f3B c z = true →
        256 < ((Finset.range 1024).filter (fun n => fzbMul c n z = fzbMul c z n)).card := by
      intro z hz h
      unfold f3B at h
      rw [Nat.blt_eq, countN_eq] at h
      convert h using 2
      refine Finset.filter_congr (fun n hn => ?_)
      have hn' : n < 1024 := Finset.mem_range.mp hn
      rw [E hn' (by omega), E (by omega) hn', Nat.beq_eq]
    have hz : z = 1 ∨ z = 2 ∨ z = 3 := by omega
    rcases hz with rfl | rfl | rfl
    · exact key 1 (by norm_num) (ch441796_f3_1 c)
    · exact key 2 (by norm_num) (ch441796_f3_2 c)
    · exact key 3 (by norm_num) (ch441796_f3_3 c)
  · intro v hv hvM hvv
    unfold fzbIsM at hvM
    rw [E hv hv] at hvv
    have h0 : v2BG c (v2G c) = true := ch441796_v2 c
    unfold v2BG at h0
    have h := (allN_iff 1024 _).mp h0 v hv
    simp only [bIf_eq, Nat.beq_eq, hvM, hvv, if_false, if_true] at h
    obtain ⟨g, -, hg⟩ := (anyL_iff _ _).mp h
    simp only [bIf_eq, Nat.blt_eq, letN_eq, Nat.beq_eq] at hg
    split_ifs at hg with hg1 hg2
    · exact ⟨g, hg1, Or.inl (by rw [E hg1 hv, E (by norm_num) hg1]; exact hg2)⟩
    · exact ⟨g, hg1, Or.inr (by rw [E hg1 hv, E (by norm_num) hg1]; exact B hg)⟩
  · intro x hx hxW y hy hyW
    obtain ⟨i, hi, rfl⟩ := (fzbW0_iff x).mp hxW
    obtain ⟨j, hj, rfl⟩ := (fzbW0_iff y).mp hyW
    rw [E hx hy, ← w0N_iff]
    exact (allN_iff 8 _).mp ((allN_iff 8 _).mp (ch441796_w0 c) i hi) j hj

theorem h1_witness {L : List Nat} (hL : e32B L = true) (hnd : L.Nodup) (hlen : L.length = 32)
    (h0 : 0 ∈ L) {n : Nat} (hn : n ∈ L) :
    ∃ S : Finset ℕ, S.card = 32 ∧ 0 ∈ S ∧
      (∀ x ∈ S, x < 1024 ∧ fzbMul true x x = 0 ∧ fzbMul true x n = fzbMul true n x) ∧
      ∀ x ∈ S, ∀ y ∈ S, fzbMul true x y = fzbMul true y x ∧ fzbMul true x y ∈ S := by
  have hA := (allL_iff _ _).mp hL
  have P : ∀ x ∈ L, x < 1024 ∧ mulN true x x = 0 ∧ ∀ y ∈ L, mulN true x y = mulN true y x ∧
      mulN true x y ∈ L := by
    intro x hx
    have h := hA x hx
    simp only [bIf_eq, Nat.blt_eq, Nat.beq_eq] at h
    split_ifs at h with h1 h2
    · refine ⟨h1, h2, fun y hy => ?_⟩
      have h' := (allL_iff _ _).mp h y hy
      simp only [letN_eq, bIf_eq, Nat.beq_eq] at h'
      split_ifs at h' with h3
      exact ⟨h3, (memL_iff _ _).mp h'⟩
    all_goals exact absurd h (by simp)
  refine ⟨L.toFinset, by rw [List.toFinset_card_of_nodup hnd, hlen], List.mem_toFinset.mpr h0,
    fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hx' := List.mem_toFinset.mp hx
    obtain ⟨hlt, hsq, hc⟩ := P x hx'
    have hnl := (P n hn).1
    refine ⟨hlt, by rw [fzbMul_eq true hlt hlt]; exact hsq, ?_⟩
    rw [fzbMul_eq true hlt hnl, fzbMul_eq true hnl hlt]
    exact (hc n hn).1
  · have hx' := List.mem_toFinset.mp hx
    have hy' := List.mem_toFinset.mp hy
    obtain ⟨hlt, -, hc⟩ := P x hx'
    have hylt := (P y hy').1
    rw [fzbMul_eq true hlt hylt, fzbMul_eq true hylt hlt, List.mem_toFinset]
    exact hc y hy'

theorem fzbH1_of : FzbH1 := by
  intro n h4 h64 hnn
  rw [fzbMul_eq true (by omega) (by omega)] at hnn
  have h0 : h1BL e32L1 e32L2 = true := ch441796_h1
  unfold h1BL at h0
  have h := (allN_iff 64 _).mp h0 n h64
  simp only [bIf_eq, Nat.blt_eq, Nat.beq_eq, hnn, if_true] at h
  rw [if_neg (by omega)] at h
  by_cases h1 : memL n e32L1 = true
  · exact h1_witness ch441796_e32_1 (by decide) rfl (by decide) ((memL_iff _ _).mp h1)
  · rw [if_neg h1] at h
    exact h1_witness ch441796_e32_2 (by decide) rfl (by decide) ((memL_iff _ _).mp h)

theorem fzbV1_of : FzbV1 := by
  intro m hm hmM hmm
  unfold fzbIsM at hmM
  have hs : fzbMul false m m < 1024 := by rw [fzbMul_eq false hm hm]; exact mulN_lt _ _ _
  rw [fzbMul_eq false hs hs, fzbMul_eq false hm hm] at hmm
  rw [fzbMul_eq false hm hm]
  have h0 := ch441796_v1
  unfold v1B at h0
  have h := (allN_iff 1024 _).mp h0 m hm
  simp only [bIf_eq, Nat.beq_eq, hmM, if_true, letN_eq, hmm, Nat.blt_eq] at h
  exact h

end CFSG.KC.FzBMod
