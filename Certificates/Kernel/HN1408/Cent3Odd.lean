module

public import Certificates.Kernel.HN1408.Cent3Perf

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cent3

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem mem_of_pow_prime {H : Type*} [Group H] (M : Subgroup H) [M.Normal] {p : ℕ}
    (hp : p.Prime) (hi : ¬ p ∣ M.index) {g : H} (hg : g ^ p = 1) : g ∈ M := by
  have h1 : orderOf (g : H ⧸ M) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one])
  have h2 : orderOf (g : H ⧸ M) ∣ M.index := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact (QuotientGroup.eq_one_iff g).1 (orderOf_eq_one_iff.1 h)
  · rw [h] at h2
    exact absurd h2 hi

theorem oddNormalAt_of_pairs {G : Type} [Group G] {x g₅ h₅ g₃ h₃ : G}
    (hcard : Nat.card (centralizer ({x} : Set G)) = 1440) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hg₅ : g₅ ∈ centralizer ({x} : Set G)) (hh₅ : h₅ ∈ centralizer ({x} : Set G))
    (pg₅ : g₅ ^ 5 = 1) (ph₅ : h₅ ^ 5 = 1) (u₅ : (g₅ * h₅) ^ 2 = 1) (u₅' : g₅ * h₅ ≠ 1)
    (hg₃ : g₃ ∈ centralizer ({x} : Set G)) (hh₃ : h₃ ∈ centralizer ({x} : Set G))
    (pg₃ : g₃ ^ 3 = 1) (ph₃ : h₃ ^ 3 = 1) (u₃ : ((g₃ * h₃) ^ 3) ^ 2 = 1)
    (u₃' : (g₃ * h₃) ^ 3 ≠ 1) :
    OddNormalAt x := by
  intro N hNC hnorm hodd
  set C := centralizer ({x} : Set G) with hCdef
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let xc : C := ⟨x, mem_centralizer_singleton_iff.2 rfl⟩
  have hcent : ∀ c : C, c * xc = xc * c := fun c => Subtype.ext (by
    have h := mem_centralizer_singleton_iff.1 c.2
    simp only [Subgroup.coe_mul]
    first | exact h | exact h.symm)
  have hx3c : xc ^ 3 = 1 := Subtype.ext (by simp [xc, hx3])
  have hx1c : xc ≠ 1 := fun e => hx1 (by simpa [xc] using congrArg Subtype.val e)
  have hox : orderOf xc = 3 := orderOf_eq_prime hx3c hx1c
  let Nh : Subgroup C := N.subgroupOf C
  let Xh : Subgroup C := zpowers xc
  have hNn : Nh.Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hnorm c c.2 n hn⟩
  have hXn : Xh.Normal := ⟨fun n hn c => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [(Commute.zpow_right (hcent c) k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers xc) k⟩
  let M : Subgroup C := Nh ⊔ Xh
  have hNcard : Nat.card Nh = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  have hpowM : ∀ y ∈ M, y ^ (Nat.card N * 3) = 1 := by
    intro y hy
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hy
    obtain ⟨n, hn, c, hc, rfl⟩ := hy
    have hcomm : Commute n c := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      exact Commute.zpow_right (hcent n) k
    have hnd : orderOf n ∣ Nat.card N * 3 :=
      (hNcard ▸ Subgroup.orderOf_dvd_natCard Nh hn).mul_right 3
    have hcd : orderOf c ∣ Nat.card N * 3 :=
      ((Subgroup.orderOf_dvd_natCard Xh hc).trans (by rw [Nat.card_zpowers, hox])).trans
        (dvd_mul_left 3 _)
    rw [hcomm.mul_pow, orderOf_dvd_iff_pow_eq_one.1 hnd, orderOf_dvd_iff_pow_eq_one.1 hcd,
      one_mul]
  have hModd : ¬ 2 ∣ Nat.card M := by
    intro h2
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 h2
    have hy2 : orderOf (y : C) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    have hd := orderOf_dvd_of_pow_eq_one (hpowM y y.2)
    rw [hy2] at hd
    have hd' : 2 ∣ Nat.card N := Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) hd
    have := Nat.odd_iff.1 hodd
    omega
  have hinv : ∀ u : C, u ∈ M → u ^ 2 = 1 → u ≠ 1 → False := fun u hu hu2 hu1 =>
    hModd (orderOf_eq_prime hu2 hu1 ▸ Subgroup.orderOf_dvd_natCard M hu)
  have hidx : M.index * Nat.card M = 1440 := by rw [Subgroup.index_mul_card, hcard]
  have h5 : ¬ 5 ∣ Nat.card M := by
    intro h5
    have hi : ¬ 5 ∣ M.index := by
      intro hi
      have := Nat.mul_dvd_mul hi h5
      rw [hidx] at this
      norm_num at this
    have hg := mem_of_pow_prime M Nat.prime_five hi (g := ⟨g₅, hg₅⟩) (Subtype.ext (by simp [pg₅]))
    have hh := mem_of_pow_prime M Nat.prime_five hi (g := ⟨h₅, hh₅⟩) (Subtype.ext (by simp [ph₅]))
    exact hinv _ (mul_mem hg hh) (Subtype.ext (by simp [u₅]))
      (fun e => u₅' (by simpa using congrArg Subtype.val e))
  have h9 : ¬ 9 ∣ Nat.card M := by
    intro h9
    have hi : ¬ 3 ∣ M.index := by
      intro hi
      have := Nat.mul_dvd_mul hi h9
      rw [hidx] at this
      norm_num at this
    have hg := mem_of_pow_prime M Nat.prime_three hi (g := ⟨g₃, hg₃⟩) (Subtype.ext (by simp [pg₃]))
    have hh := mem_of_pow_prime M Nat.prime_three hi (g := ⟨h₃, hh₃⟩) (Subtype.ext (by simp [ph₃]))
    exact hinv _ (pow_mem (mul_mem hg hh) 3) (Subtype.ext (by simp [u₃]))
      (fun e => u₃' (by simpa using congrArg Subtype.val e))
  have hM3 : Nat.card M ∣ 3 := by
    have e : (2 : ℕ) ^ 5 * 45 = 1440 := by norm_num
    have hd : Nat.card M ∣ 2 ^ 5 * 45 := by
      rw [e, ← hidx]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime (Nat.card M) (2 ^ 5) :=
      ((Nat.odd_iff.2 (by omega)).coprime_two_right).pow_right 5
    have h45 : Nat.card M ∣ 45 := hcop.dvd_of_dvd_mul_left hd
    have hle : Nat.card M ≤ 45 := Nat.le_of_dvd (by norm_num) h45
    generalize Nat.card M = d at h45 hle h5 h9 ⊢
    interval_cases d <;> omega
  have hXM : Xh ≤ M := le_sup_right
  have hXcard : Nat.card Xh = 3 := by rw [Nat.card_zpowers, hox]
  have hMX : Xh = M := Subgroup.eq_of_le_of_card_ge hXM (by
    rw [hXcard]
    exact Nat.le_of_dvd (by norm_num) hM3)
  intro n hn
  have hnM : (⟨n, hNC hn⟩ : C) ∈ Xh := by
    rw [hMX]
    exact le_sup_left (a := Nh) (Subgroup.mem_subgroupOf.2 hn)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hnM
  exact mem_zpowers_iff.2 ⟨k, by simpa [xc] using congrArg Subtype.val hk⟩

theorem el_fin {k : Nat} (hk : k < 1440) (q : Fin 1408) :
    el k q = ⟨ev k q.val, ev_lt hk q.isLt⟩ :=
  Fin.ext (el_pt hk q.isLt)

theorem pow_pt {k : Nat} (hk : k < 1440) (n : Nat) (q : Fin 1408) :
    ((el k ^ n) q).val = evPow k n q.val := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, el_fin hk]
    change ev k ((el k ^ n) q).val = ev k (evPow k n q.val)
    rw [ih]

theorem pow_el_one (hC : Nat.card cC = 1440) {k n : Nat} (hk : k < 1440)
    (h : base2 (fun p => Nat.beq (evPow k n p) p) = true) : el k ^ n = 1 := by
  obtain ⟨b0, b1⟩ := base2_parts h
  rw [← el_zero]
  refine eq_el hC (pow_mem (el_mem hk) n) (by norm_num) ?_ ?_
  · rw [pow_pt hk, ev_zero (by norm_num)]
    exact Nat.eq_of_beq_eq_true b0
  · rw [pow_pt hk, ev_zero (by norm_num)]
    exact Nat.eq_of_beq_eq_true b1

theorem pairK_parts {n g h u : Nat} (hp : pairK n g h u = true) :
    g < 1440 ∧ h < 1440 ∧ u < 1440 ∧ base2 (fun p => Nat.beq (evPow g n p) p) = true ∧
      base2 (fun p => Nat.beq (evPow h n p) p) = true ∧ invK u = true := by
  unfold pairK at hp
  obtain ⟨a, hp⟩ := mkA hp
  obtain ⟨b, hp⟩ := mkA hp
  obtain ⟨c, hp⟩ := mkA hp
  obtain ⟨-, hp⟩ := mkA hp
  obtain ⟨-, hp⟩ := mkA hp
  obtain ⟨d, hp⟩ := mkA hp
  obtain ⟨e, f⟩ := mkA hp
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp c, d, e, f⟩

theorem p5K_parts {P : Nat → Nat} (h : p5K P = true) :
    pairK 5 (P 0) (P 1) (P 2) = true ∧ mulEq (P 0) (P 1) (P 2) = true := by
  unfold p5K at h
  exact mkA h

theorem p3K_parts {P : Nat → Nat} (h : p3K P = true) :
    pairK 3 (P 0) (P 1) (P 2) = true ∧
      base2 (fun p => Nat.beq (ev (P 0) (ev (P 1) (ev (P 0) (ev (P 1) (ev (P 0) (ev (P 1) p))))))
        (ev (P 2) p)) = true := by
  unfold p3K at h
  exact mkA h

set_option maxHeartbeats 0 in
theorem odd_normal (hpf : PrimeFacts 3 [fix3]) : OddNormalAt (repP fix3) := by
  have hC := hC_of hpf
  obtain ⟨hx, hx2, hx3⟩ := x_parts hC hpf
  obtain ⟨pa5, pm5⟩ := p5K_parts ch441603_p5
  obtain ⟨g5, h5, u5, pg5, ph5, iu5⟩ := pairK_parts pa5
  obtain ⟨pa3, pb3⟩ := p3K_parts ch441603_p3
  obtain ⟨g3, h3, u3, pg3, ph3, iu3⟩ := pairK_parts pa3
  have hmul5 : el (P5 0) * el (P5 1) = el (P5 2) := el_mul hC g5 h5 u5 pm5
  have hi5 := (invK_iff hC u5).1 iu5
  have hi3 := (invK_iff hC u3).1 iu3
  have hcube : (el (P3 0) * el (P3 1)) ^ 3 = el (P3 2) := by
    obtain ⟨c0, c1⟩ := base2_parts pb3
    refine eq_el hC (pow_mem (mul_mem (el_mem g3) (el_mem h3)) 3) u3 ?_ ?_
    · simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, el_fin g3, el_fin h3]
      exact Nat.eq_of_beq_eq_true c0
    · simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, el_fin g3, el_fin h3]
      exact Nat.eq_of_beq_eq_true c1
  have memC : ∀ {k : Nat} (hk : k < 1440), elH hk ∈ centralizer ({repP fix3} : Set ↥P1408) :=
    fun hk => (mem_cent_iff hpf _).2 (by rw [elH_val]; exact el_mem hk)
  have hmap : (centralizer ({repP fix3} : Set ↥P1408)).map P1408.subtype = cC := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_cent_iff hpf y).1 hy
    · intro hg
      exact ⟨⟨g, cC_le hg⟩, (mem_cent_iff hpf _).2 hg, rfl⟩
  have hcard : Nat.card (centralizer ({repP fix3} : Set ↥P1408)) = 1440 := by
    rw [← Subgroup.card_map_of_injective P1408.subtype_injective, hmap, hC]
  have hx3' : repP fix3 ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_succ', pow_two, hx, hx2, hx3]
    rfl)
  have hx1 : repP fix3 ≠ 1 := by
    intro e
    have e1 : el (X 0) = 1 := by
      rw [← hx]
      exact congrArg Subtype.val e
    have hX0 : X 0 = 0 :=
      el_inj (xK_parts ch441603_x).1 (by norm_num) (e1.trans el_zero.symm)
    have hE0 : E 0 = 0 := (e_parts (n := 0) (by norm_num)).2.1 rfl
    exact (e_parts (n := 0) (by norm_num)).2.2.2.1 (by rw [hE0, hX0])
  refine oddNormalAt_of_pairs (g₅ := elH g5) (h₅ := elH h5) (g₃ := elH g3) (h₃ := elH h3)
    hcard hx3' hx1 (memC g5) (memC h5) ?_ ?_ ?_ ?_ (memC g3) (memC h3) ?_ ?_ ?_ ?_
  · exact Subtype.ext (by rw [Subgroup.coe_pow, elH_val]; exact pow_el_one hC g5 pg5)
  · exact Subtype.ext (by rw [Subgroup.coe_pow, elH_val]; exact pow_el_one hC h5 ph5)
  · exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul, elH_val, elH_val, hmul5, pow_two]
      exact hi5.1)
  · intro e
    apply hi5.2
    have e' := congrArg Subtype.val e
    rwa [Subgroup.coe_mul, elH_val, elH_val, hmul5] at e'
  · exact Subtype.ext (by rw [Subgroup.coe_pow, elH_val]; exact pow_el_one hC g3 pg3)
  · exact Subtype.ext (by rw [Subgroup.coe_pow, elH_val]; exact pow_el_one hC h3 ph3)
  · exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_mul, elH_val, elH_val, hcube, pow_two]
      exact hi3.1)
  · intro e
    apply hi3.2
    have e' := congrArg Subtype.val e
    rwa [Subgroup.coe_pow, Subgroup.coe_mul, elH_val, elH_val, hcube] at e'

end CFSG.KD.HN1408.Cent3

end
