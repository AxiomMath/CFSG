module

public import Certificates.Kernel.Hall82K.DAGlue
public import Certificates.Kernel.Hall82K.ML

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Hall82K CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.KC.Ord CFSG.KD.Hall82E CFSG.CGT.Hall82
open CFSG.KD.Hall82R CFSG.KD.Hall82A CFSG.ComponentClassification.AS81.Hexa
open CFSG.Monster.B.Co2 CFSG.ComponentClassification.AS81.HeTri
open CFSG.ComponentClassification.AS81.HeSylow CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem zeta_code : heZeta ∈ addSub ∧ codeL heZeta = DZC := by
  obtain ⟨-, hA, hc, -⟩ := permK_sound (andB_eq_true ch840002z).1 ch840002zc
  exact ⟨hA, hc⟩

theorem mem_hexaL_of_code {g : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) {i : ℕ} (hi : i < 1080)
    (hc : codeL g = EL i) : g ∈ hexaL := by
  obtain ⟨x, hx, hxc⟩ := hexaL_enum.2.2 i hi
  rw [code_inj hg (hexaL_enum.2.1 x hx).1 (hc.trans hxc.symm)]
  exact hx

theorem y_code : hallYP ∈ addSub ∧ codeL hallYP = YC := by
  obtain ⟨-, -, hz, -⟩ := ch840001yt
  obtain ⟨-, hA, hc, -⟩ := permK_sound ch840001yt.1 (zipArrK_getD hz 0 (by norm_num))
  exact ⟨hA, hc⟩

theorem t_code : hallTP ∈ addSub ∧ codeL hallTP = TC := by
  obtain ⟨-, -, hz, -⟩ := ch840001yt
  obtain ⟨-, hA, hc, -⟩ := permK_sound ch840001yt.2.1 (zipArrK_getD hz 1 (by norm_num))
  exact ⟨hA, hc⟩

theorem index_hexaL : (hexaL.subgroupOf hexaM).index = 2 := by
  have h := Subgroup.card_mul_index (hexaL.subgroupOf hexaM)
  have hc : Nat.card (hexaL.subgroupOf hexaM) = 1080 := by
    rw [← hexaL_enum.1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hexaL_le).toEquiv
  rw [hc, hexaM_enum.1] at h
  omega

theorem conj_mem : ∀ m ∈ hexaM, ∀ x ∈ hexaL, m * x * m⁻¹ ∈ hexaL := by
  intro m hm x hx
  have hN := Subgroup.normal_of_index_eq_two index_hexaL
  have h := hN.conj_mem ⟨x, hexaL_le hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem eq_of_card : ∀ N : Subgroup (Equiv.Perm (Fin 64)), N ≤ hexaM → Nat.card N = 1080 →
    N = hexaL := by
  intro N hN hc
  have hi : (N.subgroupOf hexaM).index = 2 := by
    have h := Subgroup.card_mul_index (N.subgroupOf hexaM)
    have hc' : Nat.card (N.subgroupOf hexaM) = 1080 := by
      rw [← hc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
    rw [hc', hexaM_enum.1] at h
    omega
  have hsq : ∀ m ∈ hexaM, m * m ∈ N := fun m hm =>
    Subgroup.mem_subgroupOf.1 (Subgroup.mul_self_mem_of_index_two hi ⟨m, hm⟩)
  obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hallLGens = [a0, a1] := ⟨_, _, rfl⟩
  have hz : zipArrK [52077576321, 61871938592] [a0, a1] = true := by
    rw [← h]
    exact ch840001enLG
  have hL : hexaL = grpN 64 [a0, a1] := by
    rw [← h]
  obtain ⟨-, hA0, hc0, -⟩ := permK_sound ch840001pk.2.2.1 (zipArrK_getD hz 0 (by norm_num))
  obtain ⟨-, hA1, hc1, -⟩ := permK_sound ch840001pk.2.2.2 (zipArrK_getD hz 1 (by norm_num))
  obtain ⟨r0, r1⟩ := andB_eq_true ch840001root
  obtain ⟨r0i, r0c⟩ := andB_eq_true r0
  obtain ⟨r1i, r1c⟩ := andB_eq_true r1
  have hroot : ∀ {g : Equiv.Perm (Fin 64)} {c i : ℕ}, g ∈ addSub → codeL g = c → i < 2160 →
      compL (EM i) (EM i) = c → g ∈ N := by
    intro g c i hg hgc hi hsqc
    obtain ⟨x, hx, hxc⟩ := hexaM_enum.2.2 i hi
    have hxA := (hexaM_enum.2.1 x hx).1
    have hgx : g = x * x := code_inj hg (addSub.mul_mem hxA hxA)
      (by rw [codeL_mul hxA hxA, hxc, hsqc, hgc])
    rw [hgx]
    exact hsq x hx
  have hle : hexaL ≤ N := by
    rw [hL]
    refine grpN_le fun a ha => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hroot hA0 hc0 (Nat.blt_eq.mp r0i) (Nat.eq_of_beq_eq_true r0c)
    · exact hroot hA1 hc1 (Nat.blt_eq.mp r1i) (Nat.eq_of_beq_eq_true r1c)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hexaL_enum.1])).symm

theorem zeta_mem : heZeta ∈ hexaL := by
  obtain ⟨hi, hc⟩ := andB_eq_true ch840001zeta
  exact mem_hexaL_of_code zeta_code.1 (Nat.blt_eq.mp hi)
    (zeta_code.2.trans (Nat.eq_of_beq_eq_true hc).symm)

theorem comm_of_code {g h : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) (hh : h ∈ addSub)
    (hc : commK (codeL g) (codeL h) = true) : g * h = h * g :=
  code_inj (addSub.mul_mem hg hh) (addSub.mul_mem hh hg)
    (by rw [codeL_mul hg hh, codeL_mul hh hg]; exact Nat.eq_of_beq_eq_true hc)

theorem commK_of_comm {g h : Equiv.Perm (Fin 64)} (hg : g ∈ addSub) (hh : h ∈ addSub)
    (hc : g * h = h * g) : commK (codeL g) (codeL h) = true := by
  unfold commK
  rw [← codeL_mul hg hh, ← codeL_mul hh hg, hc]
  exact Nat.beq_refl _

theorem mem_hexaL_iff {x : Equiv.Perm (Fin 64)} (hx : x ∈ hexaM) :
    x ∈ hexaL ↔ x * heZeta = heZeta * x := by
  set K := Subgroup.centralizer ({heZeta} : Set (Equiv.Perm (Fin 64))) ⊓ hexaM with hK
  have hmemK : ∀ y, y ∈ K ↔ y * heZeta = heZeta * y ∧ y ∈ hexaM := by
    intro y
    rw [hK, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
  have hLK : hexaL ≤ K := by
    obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hallLGens = [a0, a1] := ⟨_, _, rfl⟩
    have hz : zipArrK [52077576321, 61871938592] [a0, a1] = true := by
      rw [← h]
      exact ch840001enLG
    have hL : hexaL = grpN 64 [a0, a1] := by
      rw [← h]
    obtain ⟨-, hA0, hc0, -⟩ := permK_sound ch840001pk.2.2.1 (zipArrK_getD hz 0 (by norm_num))
    obtain ⟨-, hA1, hc1, -⟩ := permK_sound ch840001pk.2.2.2 (zipArrK_getD hz 1 (by norm_num))
    have hm0 : permOfArr 64 a0 ∈ hexaL := by
      rw [hL]
      exact Subgroup.subset_closure ⟨0, by simp, rfl⟩
    have hm1 : permOfArr 64 a1 ∈ hexaL := by
      rw [hL]
      exact Subgroup.subset_closure ⟨1, by simp, rfl⟩
    rw [hL]
    refine grpN_le fun a ha => ?_
    rw [hmemK]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · refine ⟨comm_of_code hA0 zeta_code.1 ?_, hexaL_le hm0⟩
      have e : codeL ⇑(permOfArr 64 a) = 52077576321 := hc0
      rw [e, zeta_code.2]
      exact ch840001comm.1
    · refine ⟨comm_of_code hA1 zeta_code.1 ?_, hexaL_le hm1⟩
      have e : codeL ⇑(permOfArr 64 a) = 61871938592 := hc1
      rw [e, zeta_code.2]
      exact ch840001comm.2.1
  have hKM : K ≤ hexaM := inf_le_right
  have hKne : K ≠ hexaM := by
    intro hKeq
    obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hexaMGens = [a0, a1] := ⟨_, _, rfl⟩
    have hz : zipArrK [4439643498, 34633937090] [a0, a1] = true := by
      rw [← h]
      exact ch840004mg_code
    obtain ⟨-, hA0, hc0, -⟩ := permK_sound ch840001pk.1 (zipArrK_getD hz 0 (by norm_num))
    have hm : permOfArr 64 a0 ∈ hexaM := by
      change permOfArr 64 a0 ∈ grpN 64 hexaMGens
      rw [h]
      exact Subgroup.subset_closure ⟨0, by simp, rfl⟩
    have hk := ((hmemK _).1 (hKeq ▸ hm)).1
    have hb := commK_of_comm hA0 zeta_code.1 hk
    rw [hc0, zeta_code.2, ch840001comm.2.2] at hb
    exact Bool.noConfusion hb
  have hKL : K = hexaL := by
    obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le hLK
    obtain ⟨b, hb⟩ := Subgroup.card_dvd_of_le hKM
    rw [hexaL_enum.1] at ha
    rw [hexaM_enum.1, ha] at hb
    have hab : a * b = 2 := by nlinarith
    have ha2 : a ≤ 2 := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0] at hab
        omega
      · nlinarith
    interval_cases a
    · omega
    · exact (Subgroup.eq_of_le_of_card_ge hLK (by rw [ha, hexaL_enum.1])).symm
    · exact absurd (Subgroup.eq_of_le_of_card_ge hKM (by rw [ha, hexaM_enum.1])) hKne
  constructor
  · intro hxL
    exact ((hmemK x).1 (hLK hxL)).1
  · intro hc
    rw [← hKL]
    exact (hmemK x).2 ⟨hc, hx⟩

theorem center : ∀ x ∈ hexaL, (∀ y ∈ hexaL, x * y = y * x) → x ∈ Subgroup.zpowers heZeta := by
  intro x hx hcen
  obtain ⟨hxA, k, hk, hxk⟩ := hexaL_enum.2.1 x hx
  have hchk := (allN_iff _ _).1 ch840001center k hk
  simp only [centerAtK, letB_eq] at hchk
  rw [← hxk] at hchk
  obtain ⟨hzA, hzc⟩ := zeta_code
  rcases orB_eq_true82 hchk with h3 | hw
  · rcases orB_eq_true82 h3 with h1 | h3
    · rw [code_inj hxA addSub.one_mem (Nat.eq_of_beq_eq_true h1)]
      exact Subgroup.one_mem _
    rcases orB_eq_true82 h3 with hz | hz2
    · rw [code_inj hxA hzA ((Nat.eq_of_beq_eq_true hz).trans hzc.symm)]
      exact Subgroup.mem_zpowers _
    · have e : x = heZeta * heZeta := code_inj hxA (addSub.mul_mem hzA hzA)
        (by rw [codeL_mul hzA hzA, hzc]; exact Nat.eq_of_beq_eq_true hz2)
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  · exfalso
    obtain ⟨hj, hn⟩ := andB_eq_true hw
    obtain ⟨y, hy, hyc⟩ := hexaL_enum.2.2 _ (Nat.blt_eq.mp hj)
    have hyA := (hexaL_enum.2.1 y hy).1
    have hb := commK_of_comm hxA hyA (hcen y hy)
    rw [hyc] at hb
    have h := negK_eq_true hn
    rw [hb] at h
    exact Bool.noConfusion h

theorem eq_bot : ∀ X : Subgroup (Equiv.Perm (Fin 64)), X ≤ hexaM → IsPGroup 2 X →
    (∀ a ∈ hexaL, ∀ x ∈ X, a * x * a⁻¹ ∈ X) → X = ⊥ := by
  intro X hX h2 hnorm
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨hxA, k, hk, hxk⟩ := hexaM_enum.2.1 x (hX hx)
  have hchk := (allN_iff _ _).1 ch840001nv k hk
  simp only [nvAtZK, letB_eq] at hchk
  rw [← hxk] at hchk
  have hn : negK (Nat.beq (codeL x) idK) = true := by
    cases h : Nat.beq (codeL x) idK
    · rfl
    · exact absurd (code_inj hxA addSub.one_mem (Nat.eq_of_beq_eq_true h)) hne
  have hp : Nat.beq (powL (codeL x) 16) idK = true := by
    rw [← codeL_pow hxA, pow16_of_two hX h2 hx, codeL_one]
    exact Nat.beq_refl _
  have hw := impB_eq_true hchk (by rw [hn, hp]; rfl)
  simp only [nvWitZK, letB_eq] at hw
  obtain ⟨hw1, hw⟩ := andB_eq_true hw
  obtain ⟨hw2, hw⟩ := andB_eq_true hw
  obtain ⟨hw4, hw5⟩ := andB_eq_true hw
  obtain ⟨a, haL, haA, hac, haic⟩ :=
    exists_hexaL_pair (Nat.blt_eq.mp hw1) (Nat.blt_eq.mp hw2) (Nat.eq_of_beq_eq_true hw4)
  have hz : a * x * a⁻¹ ∈ X := hnorm a haL x hx
  have hq : x * (a * x * a⁻¹) ^ 15 ∈ X := X.mul_mem hx (X.pow_mem hz 15)
  have hq16 := pow16_of_two hX h2 hq
  have hzA : a * x * a⁻¹ ∈ addSub :=
    addSub.mul_mem (addSub.mul_mem haA hxA) (addSub.inv_mem haA)
  have hqA : x * (a * x * a⁻¹) ^ 15 ∈ addSub := addSub.mul_mem hxA (addSub.pow_mem hzA 15)
  have hcode := codeL_pow hqA 16
  rw [hq16, codeL_one, codeL_mul hxA (addSub.pow_mem hzA 15), codeL_pow hzA,
    codeL_mul (addSub.mul_mem haA hxA) (addSub.inv_mem haA), codeL_mul haA hxA, hac,
    haic] at hcode
  have h := negK_eq_true hw5
  rw [← hcode, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem fixPts_le_8 : ∀ x ∈ hexaM, x ∉ hexaL → x * x = 1 → Nat.card (fixPts {x}) ≤ 8 := by
  intro x hx hxL hxx
  obtain ⟨hxA, k, hk, hxk⟩ := hexaM_enum.2.1 x hx
  have hchk := (allN_iff _ _).1 ch840001fix8 k hk
  simp only [fix8AtK, letB_eq] at hchk
  rw [← hxk] at hchk
  have hsq : Nat.beq (compL (codeL x) (codeL x)) idK = true := by
    rw [← codeL_mul hxA hxA, hxx, codeL_one]
    exact Nat.beq_refl _
  have hnc : negK (commK (codeL x) DZC) = true := by
    cases h : commK (codeL x) DZC
    · rfl
    · exfalso
      rw [← zeta_code.2] at h
      exact hxL ((mem_hexaL_iff hx).2 (comm_of_code hxA zeta_code.1 h))
  have hall := impB_eq_true hchk (by rw [hsq, hnc]; rfl)
  set f := lane (lane MF8 48 281474976710655 k) 6 63 with hf
  let g : Fin 8 → Fin 64 := fun i =>
    ⟨lane (lane MF8 48 281474976710655 k) 6 63 i.val,
      lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩
  have hsub : fixPts {x} ⊆ Set.range g := by
    intro v hv
    have hxv : x v = v := hv x rfl
    have hv' := impB_eq_true ((allN_iff _ _).1 hall v.val v.2)
      (by rw [← apL_code hxA, hxv]; exact Nat.beq_refl _)
    obtain ⟨i, hi, he⟩ := (anyN_iff _ _).1 hv'
    exact ⟨⟨i, hi⟩, Fin.ext (Nat.eq_of_beq_eq_true he)⟩
  calc Nat.card (fixPts {x}) ≤ Nat.card (Set.range g) := Nat.card_mono (Set.finite_range g) hsub
    _ ≤ Nat.card (Fin 8) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = 8 := by simp

theorem conj_t : ∀ x ∈ hexaL, x * x = 1 → x ≠ 1 → ∃ a ∈ hexaL, a * hallTP * a⁻¹ = x := by
  intro x hx hxx hne
  obtain ⟨hxA, k, hk, hxk⟩ := hexaL_enum.2.1 x hx
  have hchk := (allN_iff _ _).1 ch840001conjT k hk
  simp only [conjTAtK, letB_eq] at hchk
  rw [← hxk] at hchk
  have hn : negK (Nat.beq (codeL x) idK) = true := by
    cases h : Nat.beq (codeL x) idK
    · rfl
    · exact absurd (code_inj hxA addSub.one_mem (Nat.eq_of_beq_eq_true h)) hne
  have hsq : Nat.beq (compL (codeL x) (codeL x)) idK = true := by
    rw [← codeL_mul hxA hxA, hxx, codeL_one]
    exact Nat.beq_refl _
  have hw := impB_eq_true hchk (by rw [hn, hsq]; rfl)
  obtain ⟨hw1, hw⟩ := andB_eq_true hw
  obtain ⟨hw2, hw⟩ := andB_eq_true hw
  obtain ⟨hw3, hw4⟩ := andB_eq_true hw
  obtain ⟨a, haL, haA, hac, haic⟩ :=
    exists_hexaL_pair (Nat.blt_eq.mp hw1) (Nat.blt_eq.mp hw2) (Nat.eq_of_beq_eq_true hw3)
  obtain ⟨htA, htc⟩ := t_code
  refine ⟨a, haL, code_inj (addSub.mul_mem (addSub.mul_mem haA htA) (addSub.inv_mem haA)) hxA ?_⟩
  rw [codeL_mul (addSub.mul_mem haA htA) (addSub.inv_mem haA), codeL_mul haA htA, hac, haic, htc]
  exact Nat.eq_of_beq_eq_true hw4

theorem y_mem : hallYP ∈ hexaL := by
  obtain ⟨-, -, -, h, -⟩ := ch840001yt
  obtain ⟨hi, hc⟩ := andB_eq_true h
  exact mem_hexaL_of_code y_code.1 (Nat.blt_eq.mp hi) (y_code.2.trans (Nat.eq_of_beq_eq_true hc).symm)

theorem t_mem : hallTP ∈ hexaL := by
  obtain ⟨-, -, -, -, h, -⟩ := ch840001yt
  obtain ⟨hi, hc⟩ := andB_eq_true h
  exact mem_hexaL_of_code t_code.1 (Nat.blt_eq.mp hi) (t_code.2.trans (Nat.eq_of_beq_eq_true hc).symm)

theorem t_mul_t : hallTP * hallTP = 1 := by
  obtain ⟨-, -, -, -, -, h, -⟩ := ch840001yt
  obtain ⟨htA, htc⟩ := t_code
  exact code_inj (addSub.mul_mem htA htA) addSub.one_mem (by rw [codeL_mul htA htA, htc, h]; rfl)

theorem y_pow_four : hallYP ^ 4 = 1 := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := ch840001yt
  obtain ⟨hyA, hyc⟩ := y_code
  exact code_inj (addSub.pow_mem hyA 4) addSub.one_mem (by rw [codeL_pow hyA, hyc, h]; rfl)

theorem y_sq_ne_one : hallYP ^ 2 ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := ch840001yt
  obtain ⟨hyA, hyc⟩ := y_code
  intro he
  have hc := codeL_pow hyA 2
  rw [he, codeL_one, hyc] at hc
  have h' := negK_eq_true h
  rw [← hc, Nat.beq_refl] at h'
  exact Bool.noConfusion h'

theorem ty_mul_ty : (hallTP * hallYP) * (hallTP * hallYP) = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := ch840001yt
  obtain ⟨hyA, hyc⟩ := y_code
  obtain ⟨htA, htc⟩ := t_code
  have hA := addSub.mul_mem htA hyA
  exact code_inj (addSub.mul_mem hA hA) addSub.one_mem
    (by rw [codeL_mul hA hA, codeL_mul htA hyA, hyc, htc, h]; rfl)

theorem permsA_hallYT :
    permsA 64 [hallY, hallT].toArray = ({hallYP, hallTP} : Set (Equiv.Perm (Fin 64))) := by
  ext x
  simp only [permsA, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa using hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem card_closure :
    Nat.card (Subgroup.closure ({hallYP, hallTP} : Set (Equiv.Perm (Fin 64)))) = 8 := by
  have h : Subgroup.closure ({hallYP, hallTP} : Set (Equiv.Perm (Fin 64))) =
      grpN 64 [hallY, hallT] := by
    rw [grpN, permsA_hallYT]
  obtain ⟨hpy, hpt, hz, -⟩ := ch840001yt
  rw [h]
  exact (enum_sound hz hpy hpt (by norm_num) fun k hk => (allN_iff _ _).1 ch840001ytEnum k hk).1

end CFSG.KD.Hall82L
