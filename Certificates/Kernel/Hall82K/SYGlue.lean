module

public import Certificates.Kernel.Hall82K.MRGlue
public import Certificates.Kernel.Hall82K.SY
public import CFSG.Certificates.Kernel.F4M3BSound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Hall82K CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.KC.Ord CFSG.KD.Hall82E CFSG.CGT.Hall82
open CFSG.KD.Hall82R CFSG.KD.Hall82A CFSG.ComponentClassification.AS81.Hexa CFSG.KC.F4M3B
open CFSG.Monster.B.Co2 CFSG.ComponentClassification.AS81.HeTri

theorem sy_parts : syE EM SYI 0 = idK ∧ ∀ i < 16, lane SYI 12 4095 i < 2160 ∧ ∀ j < 16,
    compL (syE EM SYI i) (syE EM SYI j) = syE EM SYI (syT SYT i j) ∧
      (syE EM SYI i = syE EM SYI j → i = j) := by
  obtain ⟨h0, h1⟩ := andB_eq_true ch840001syB
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi => ?_⟩
  obtain ⟨hl, h2⟩ := andB_eq_true ((allN_iff _ _).1 h1 i hi)
  refine ⟨Nat.blt_eq.mp hl, fun j hj => ?_⟩
  obtain ⟨hm, hd⟩ := andB_eq_true ((allN_iff _ _).1 h2 j hj)
  exact ⟨Nat.eq_of_beq_eq_true hm, fun h => Nat.eq_of_beq_eq_true
    (impB_eq_true hd (by rw [h]; exact Nat.beq_refl _))⟩

theorem syT_lt (i j : ℕ) : syT SYT i j < 16 := Nat.lt_succ_of_le Nat.and_le_right

theorem sy_exists (i : Fin 16) : ∃ g ∈ hexaM, codeL g = syE EM SYI i.val :=
  hexaM_enum.2.2 _ (sy_parts.2 i.val i.2).1

noncomputable def sP (i : Fin 16) : Equiv.Perm (Fin 64) := (sy_exists i).choose

theorem sP_mem (i : Fin 16) : sP i ∈ hexaM := (sy_exists i).choose_spec.1

theorem sP_code (i : Fin 16) : codeL (sP i) = syE EM SYI i.val := (sy_exists i).choose_spec.2

theorem sP_add (i : Fin 16) : sP i ∈ addSub := (hexaM_enum.2.1 _ (sP_mem i)).1

theorem sP_val (i : Fin 16) (v : Fin 64) : (sP i v).val = apL (syE EM SYI i.val) v.val := by
  rw [apL_code (sP_add i), sP_code]

theorem sP_mul (i j : Fin 16) : sP i * sP j = sP ⟨syT SYT i j, syT_lt _ _⟩ :=
  code_inj (addSub.mul_mem (sP_add i) (sP_add j)) (sP_add _)
    (by
      rw [codeL_mul (sP_add i) (sP_add j), sP_code, sP_code, sP_code]
      exact ((sy_parts.2 i i.2).2 j j.2).1)

theorem sP_zero : sP 0 = 1 :=
  code_inj (sP_add 0) addSub.one_mem (by rw [sP_code, codeL_one]; exact sy_parts.1)

theorem sP_inj : Function.Injective sP := by
  intro i j h
  have hc : syE EM SYI i.val = syE EM SYI j.val := by rw [← sP_code, ← sP_code, h]
  exact Fin.ext (((sy_parts.2 i i.2).2 j j.2).2 hc)

theorem range_mul {x y : Equiv.Perm (Fin 64)} (hx : x ∈ Set.range sP) (hy : y ∈ Set.range sP) :
    x * y ∈ Set.range sP := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact ⟨_, (sP_mul i j).symm⟩

theorem range_pow {x : Equiv.Perm (Fin 64)} (hx : x ∈ Set.range sP) :
    ∀ n, x ^ n ∈ Set.range sP
  | 0 => ⟨0, by rw [sP_zero, pow_zero]⟩
  | n + 1 => by
    rw [pow_succ]
    exact range_mul (range_pow hx n) hx

def sigma : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := Set.range sP
  one_mem' := ⟨0, sP_zero⟩
  mul_mem' := range_mul
  inv_mem' := fun {x} hx => by
    have hpos := orderOf_pos x
    have h : x⁻¹ = x ^ (orderOf x - 1) := inv_eq_of_mul_eq_one_right (by
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one])
    rw [h]
    exact range_pow hx _

theorem mem_sigma {x : Equiv.Perm (Fin 64)} : x ∈ sigma ↔ ∃ i, sP i = x := Iff.rfl

theorem card_sigma : Nat.card sigma = 16 := by
  change Nat.card (Set.range sP) = 16
  rw [Nat.card_range_of_injective sP_inj]
  simp

theorem sigma_le : sigma ≤ hexaM := by
  rintro _ ⟨i, rfl⟩
  exact sP_mem i

theorem factorization_2160K : (2160 : ℕ).factorization 2 = 4 := by
  have h : (2160 : ℕ) = 2 ^ 4 * 135 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 135)]

noncomputable def sigmaSylow : Sylow 2 ↥hexaM :=
  Sylow.ofCard (sigma.subgroupOf hexaM) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sigma_le).toEquiv, card_sigma,
      hexaM_enum.1, factorization_2160K]
    norm_num)

theorem le_sigma_conj {B : Subgroup (Equiv.Perm (Fin 64))} (hB : B ≤ hexaM) (h2 : IsPGroup 2 B) :
    ∃ m : Equiv.Perm (Fin 64), m ∈ hexaM ∧ B.map (MulAut.conj m).toMonoidHom ≤ sigma := by
  have hBG2 : IsPGroup 2 (B.subgroupOf hexaM) :=
    IsPGroup.comap_of_injective h2 hexaM.subtype Subtype.val_injective
  obtain ⟨P, hBP⟩ := IsPGroup.exists_le_sylow hBG2
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥hexaM) P sigmaSylow
  have hG : (B.subgroupOf hexaM).map (MulAut.conj g).toMonoidHom ≤ sigma.subgroupOf hexaM := by
    calc (B.subgroupOf hexaM).map (MulAut.conj g).toMonoidHom
        ≤ P.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hBP
      _ = (↑(g • P) : Subgroup ↥hexaM) := by
          rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
          rfl
      _ = sigma.subgroupOf hexaM := by rw [hg, sigmaSylow, Sylow.coe_ofCard]
  refine ⟨(g : Equiv.Perm (Fin 64)), g.2, ?_⟩
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
  have hmem : ((MulAut.conj g) (⟨b, hB hb⟩ : ↥hexaM) : ↥hexaM) ∈ sigma.subgroupOf hexaM :=
    hG (Subgroup.mem_map.2 ⟨⟨b, hB hb⟩, hb, rfl⟩)
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem onesK_eq : onesK = 2 ^ 65536 - 1 := by decide +kernel

theorem testBit_onesK {m : ℕ} (hm : m < 65536) : onesK.testBit m = true := by
  rw [onesK_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hm

theorem testBit_clPair {T i j m : ℕ} (hm : m < 65536) :
    (clPair T i j).testBit m =
      (!(m.testBit i) || !(m.testBit j) || m.testBit (syT T i j)) := by
  have hm' : m < 2 ^ 16 := hm
  unfold clPair
  change ((pln i 16 ^^^ onesK) ||| ((pln j 16 ^^^ onesK) ||| pln (syT T i j) 16)).testBit m = _
  simp only [Nat.testBit_lor, Nat.testBit_xor, pln_bit, testBit_onesK hm, decide_eq_true hm',
    Bool.true_and, Bool.xor_true, Bool.or_assoc]

theorem testBit_clRec {T m o : ℕ} (ho : o.testBit m = true) : ∀ n,
    (Nat.rec (motive := fun _ => ℕ) o
      (fun k acc => Nat.land acc (clPair T (Nat.div k 16) (Nat.mod k 16))) n).testBit m = true ↔
      ∀ k < n, (clPair T (k / 16) (k % 16)).testBit m = true
  | 0 => by
    change o.testBit m = true ↔ _
    simp [ho]
  | n + 1 => by
    change ((Nat.rec (motive := fun _ => ℕ) o
      (fun k acc => Nat.land acc (clPair T (Nat.div k 16) (Nat.mod k 16))) n) &&&
        clPair T (n / 16) (n % 16)).testBit m = true ↔ _
    rw [Nat.testBit_land, Bool.and_eq_true, testBit_clRec ho n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

theorem testBit_clPl {T m : ℕ} (hm : m < 65536) :
    (clPl T).testBit m = true ↔ ∀ k < 256, (clPair T (k / 16) (k % 16)).testBit m = true := by
  have h := testBit_clRec (T := T) (m := m) (o := onesK) (testBit_onesK hm) 256
  unfold clPl
  exact h

theorem mem_of_testBit_xorPow : ∀ (L : List ℕ) (x : ℕ), (xorPow L).testBit x = true → x ∈ L
  | [], x, h => by
    change Nat.testBit 0 x = true at h
    simp at h
  | m :: L, x, h => by
    change (Nat.xor (Nat.shiftLeft 1 m) (xorPow L)).testBit x = true at h
    have e : Nat.shiftLeft 1 m = 2 ^ m := by
      change 1 <<< m = 2 ^ m
      rw [Nat.shiftLeft_eq, one_mul]
    rw [e] at h
    change ((2 ^ m) ^^^ xorPow L).testBit x = true at h
    rw [Nat.testBit_xor, Nat.testBit_two_pow] at h
    by_cases hx : m = x
    · rw [hx]
      exact List.mem_cons_self
    · rw [decide_eq_false hx, Bool.false_xor] at h
      exact List.mem_cons_of_mem _ (mem_of_testBit_xorPow L x h)

theorem syList_mem : ∀ L : List ℕ, syListK EM SYI DZC L = true → ∀ m ∈ L,
    syCondK EM SYI DZC m = true
  | [], _, m, hm => absurd hm List.not_mem_nil
  | a :: L, h, m, hm => by
    change andB (syCondK EM SYI DZC a) (syListK EM SYI DZC L) = true at h
    obtain ⟨h1, h2⟩ := andB_eq_true h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h1
    · exact syList_mem L h2 m hm

theorem inS_maskOf (p : ℕ → Bool) {n e : ℕ} (he : e < n) : inS (maskOf p n) e = p e := by
  unfold inS
  rw [bitN_eq82, testBit_maskOf p n e he]
  cases p e <;> rfl

theorem sub_sigma (B : Subgroup (Equiv.Perm (Fin 64))) (hB : B ≤ sigma) :
    Nat.card B * Nat.card (fixPts B) ≤ 64 ∧
      ((∀ b ∈ B, b * heZeta = heZeta * b) ∨ Nat.card B * Nat.card (fixPts B) ≤ 32) ∧
      (Nat.card B < 4 ∨ (∃ b ∈ B, b ≠ 1 ∧ Nat.card (fixPts {b}) ≠ Nat.card (fixPts B)) ∨
        (Nat.card B = 4 ∧ (∀ b ∈ B, b * heZeta = heZeta * b) ∧ (∀ b ∈ B, b * b = 1) ∧
          Nat.card (fixPts B) = 16)) := by
  classical
  let p : ℕ → Bool := fun e => if h : e < 16 then decide (sP ⟨e, h⟩ ∈ B) else false
  let m := maskOf p 16
  have hm : ∀ e : Fin 16, inS m e.val = true ↔ sP e ∈ B := by
    intro e
    rw [inS_maskOf p e.2]
    simp [p, e.2]
  have hm16 : m < 65536 := by
    have h := maskOf_lt p 16
    norm_num at h
    exact h
  have hbit : ∀ e : Fin 16, m.testBit e.val = true ↔ sP e ∈ B := by
    intro e
    rw [testBit_maskOf p 16 e.val e.2]
    simp [p, e.2]
  have hcl : (clPl SYT).testBit m = true := by
    refine (testBit_clPl hm16).2 fun k hk => ?_
    rw [testBit_clPair hm16]
    have hi : k / 16 < 16 := by omega
    have hj : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
    cases h1 : m.testBit (k / 16)
    · rfl
    cases h2 : m.testBit (k % 16)
    · rfl
    have hiB := (hbit ⟨_, hi⟩).1 h1
    have hjB := (hbit ⟨_, hj⟩).1 h2
    have hp := B.mul_mem hiB hjB
    rw [sP_mul] at hp
    simp only [Bool.not_true, Bool.false_or]
    exact (hbit ⟨_, syT_lt _ _⟩).2 hp
  have hmL : m ∈ SYL := by
    have h := ch840001syCl
    unfold syClK at h
    have he : clPl SYT = xorPow SYL := Nat.eq_of_beq_eq_true h
    rw [he] at hcl
    exact mem_of_testBit_xorPow _ _ hcl
  have hc := syList_mem SYL ch840001syL m hmL
  simp only [syCondK, letB_eq] at hc
  have himg : (B : Set (Equiv.Perm (Fin 64))) = sP '' {e | inS m e.val = true} := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, rfl⟩ := mem_sigma.1 (hB hx)
      exact ⟨e, (hm e).2 hx, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact (hm e).1 he
  have hcardB : Nat.card B = cntK (inS m) 16 := by
    change Nat.card (B : Set (Equiv.Perm (Fin 64))) = _
    rw [himg, Nat.card_image_of_injective sP_inj]
    exact natCard_eq_cntK (inS m) _ fun _ => Iff.rfl
  have hcardF : Nat.card (fixPts (B : Set (Equiv.Perm (Fin 64)))) = fixSK EM SYI m := by
    refine natCard_eq_cntK _ _ fun v => ?_
    constructor
    · intro hv
      refine (allN_iff _ _).2 fun e he => impB_of fun hme => ?_
      have h := hv _ ((hm ⟨e, he⟩).1 hme)
      have hval := sP_val ⟨e, he⟩ v
      rw [h] at hval
      rw [← hval]
      exact Nat.beq_refl _
    · intro hv b hb
      obtain ⟨e, rfl⟩ := mem_sigma.1 (hB hb)
      have h := impB_eq_true ((allN_iff _ _).1 hv e.val e.2) ((hm e).2 hb)
      exact Fin.ext ((sP_val e v).trans (Nat.eq_of_beq_eq_true h))
  have hfix1 : ∀ e : Fin 16, Nat.card (fixPts {sP e}) =
      cntK (fun v => Nat.beq (apL (syE EM SYI e.val) v) v) 64 := by
    intro e
    refine natCard_eq_cntK _ _ fun v => ?_
    constructor
    · intro hv
      have h := hv (sP e) rfl
      have hval := sP_val e v
      rw [h] at hval
      rw [← hval]
      exact Nat.beq_refl _
    · intro hv b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact Fin.ext ((sP_val e v).trans (Nat.eq_of_beq_eq_true hv))
  have hallZ : allZK EM SYI DZC m = true → ∀ b ∈ B, b * heZeta = heZeta * b := by
    intro h b hb
    obtain ⟨e, rfl⟩ := mem_sigma.1 (hB hb)
    have hc := impB_eq_true ((allN_iff _ _).1 h e.val e.2) ((hm e).2 hb)
    rw [← sP_code, ← zeta_code.2] at hc
    exact comm_of_code (sP_add e) zeta_code.1 hc
  have hallSq : allSqK EM SYI m = true → ∀ b ∈ B, b * b = 1 := by
    intro h b hb
    obtain ⟨e, rfl⟩ := mem_sigma.1 (hB hb)
    have hc := impB_eq_true ((allN_iff _ _).1 h e.val e.2) ((hm e).2 hb)
    exact code_inj (addSub.mul_mem (sP_add e) (sP_add e)) addSub.one_mem
      (by rw [codeL_mul (sP_add e) (sP_add e), sP_code, codeL_one]; exact Nat.eq_of_beq_eq_true hc)
  obtain ⟨h64, hc⟩ := andB_eq_true hc
  obtain ⟨h32, h4⟩ := andB_eq_true hc
  rw [← hcardB, ← hcardF] at h64 h32 h4
  refine ⟨Nat.le_of_ble_eq_true h64, ?_, ?_⟩
  · rcases orB_eq_true82 h32 with h | h
    · exact Or.inl (hallZ h)
    · exact Or.inr (Nat.le_of_ble_eq_true h)
  · rcases orB_eq_true82 h4 with h | h
    · exact Or.inl (Nat.blt_eq.mp h)
    rcases orB_eq_true82 h with h | h
    · obtain ⟨e, he, h⟩ := (anyN_iff _ _).1 h
      obtain ⟨heB, h⟩ := andB_eq_true h
      obtain ⟨he0, hne⟩ := andB_eq_true h
      refine Or.inr (Or.inl ⟨sP ⟨e, he⟩, (hm ⟨e, he⟩).1 heB, ?_, ?_⟩)
      · intro h1
        rw [← sP_zero] at h1
        have e0 : e = 0 := congrArg Fin.val (sP_inj h1)
        have h' := negK_eq_true he0
        rw [e0, Nat.beq_refl] at h'
        exact Bool.noConfusion h'
      · intro hE
        rw [hfix1] at hE
        have h' := negK_eq_true hne
        rw [hE, Nat.beq_refl] at h'
        exact Bool.noConfusion h'
    · obtain ⟨hc4, h⟩ := andB_eq_true h
      obtain ⟨hz, h⟩ := andB_eq_true h
      obtain ⟨hsq, h16⟩ := andB_eq_true h
      exact Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true hc4, hallZ hz, hallSq hsq,
        Nat.eq_of_beq_eq_true h16⟩)

theorem le_map_conj_hexaL_iffK {B : Subgroup (Equiv.Perm (Fin 64))} {m : Equiv.Perm (Fin 64)}
    (hm : m ∈ hexaM) : B.map (MulAut.conj m).toMonoidHom ≤ hexaL ↔ B ≤ hexaL := by
  constructor
  · intro h b hb
    have h1 : m * b * m⁻¹ ∈ hexaL := h (Subgroup.mem_map.2 ⟨b, hb, rfl⟩)
    have h2 := conj_mem m⁻¹ (hexaM.inv_mem hm) _ h1
    simpa [mul_assoc] using h2
  · intro h b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    exact conj_mem m hm _ (h hb₀)

theorem sq_map_conj_iffK (B : Subgroup (Equiv.Perm (Fin 64))) (m : Equiv.Perm (Fin 64)) :
    (∀ b ∈ B.map (MulAut.conj m).toMonoidHom, b * b = 1) ↔ (∀ b ∈ B, b * b = 1) := by
  constructor
  · intro h b hb
    have h1 := h (m * b * m⁻¹) (Subgroup.mem_map.2 ⟨b, hb, rfl⟩)
    have h2 : m * (b * b) * m⁻¹ = 1 := by
      calc m * (b * b) * m⁻¹ = (m * b * m⁻¹) * (m * b * m⁻¹) := by group
        _ = 1 := h1
    calc b * b = m⁻¹ * (m * (b * b) * m⁻¹) * m := by group
      _ = 1 := by rw [h2]; group
  · intro h b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    calc (m * b₀ * m⁻¹) * (m * b₀ * m⁻¹) = m * (b₀ * b₀) * m⁻¹ := by group
      _ = 1 := by rw [h b₀ hb₀]; group

theorem fixPts_singleton_map_conjK {B : Subgroup (Equiv.Perm (Fin 64))} {m : Equiv.Perm (Fin 64)}
    (h : ∀ b ∈ B, b ≠ 1 → fixPts ({b} : Set (Equiv.Perm (Fin 64))) = fixPts (B : Set _)) :
    ∀ b ∈ B.map (MulAut.conj m).toMonoidHom, b ≠ 1 →
      fixPts ({b} : Set (Equiv.Perm (Fin 64))) =
        fixPts ((B.map (MulAut.conj m).toMonoidHom : Subgroup (Equiv.Perm (Fin 64))) :
          Set (Equiv.Perm (Fin 64))) := by
  intro b hb hb1
  obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
  have hb₀1 : b₀ ≠ 1 := by
    intro h0
    exact hb1 (by rw [h0, map_one])
  have hb_eq : ((MulAut.conj m).toMonoidHom) b₀ = m * b₀ * m⁻¹ := MulAut.conj_apply ..
  rw [hb_eq]
  have e1 : ({m * b₀ * m⁻¹} : Set (Equiv.Perm (Fin 64))) =
      (fun b => m * b * m⁻¹) '' ({b₀} : Set (Equiv.Perm (Fin 64))) := by
    ext x
    simp [MulAut.conj_apply]
  rw [e1, fixPts_conj_imageK, h b₀ hb₀ hb₀1, ← fixPts_conj_imageK, ← coe_map_conjK]

theorem le_64 : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B →
    Nat.card B * Nat.card (fixPts B) ≤ 64 := by
  intro B hB h2
  obtain ⟨m, -, hle⟩ := le_sigma_conj hB h2
  have h := (sub_sigma _ hle).1
  rwa [card_map_conjK, card_fixPts_map_conjK] at h

theorem le_32_of_not_le : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B →
    ¬ B ≤ hexaL → Nat.card B * Nat.card (fixPts B) ≤ 32 := by
  intro B hB h2 hnB
  obtain ⟨m, hm, hle⟩ := le_sigma_conj hB h2
  rcases (sub_sigma _ hle).2.1 with h | h
  · exfalso
    apply hnB
    rw [← le_map_conj_hexaL_iffK hm]
    intro b hb
    exact (mem_hexaL_iff (sigma_le (hle hb))).2 (h b hb)
  · rwa [card_map_conjK, card_fixPts_map_conjK] at h

theorem of_fixPts_eq : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B →
    4 ≤ Nat.card B → (∀ b ∈ B, b ≠ 1 → fixPts {b} = fixPts B) →
      B ≤ hexaL ∧ Nat.card B = 4 ∧ (∀ b ∈ B, b * b = 1) ∧ Nat.card (fixPts B) = 16 := by
  intro B hB h2 h4 hfix
  obtain ⟨m, hm, hle⟩ := le_sigma_conj hB h2
  have hfix' := fixPts_singleton_map_conjK (m := m) hfix
  rcases (sub_sigma _ hle).2.2 with h | h | h
  · rw [card_map_conjK] at h
    omega
  · obtain ⟨b, hb, hb1, hne⟩ := h
    exact absurd (by rw [hfix' b hb hb1]) hne
  · obtain ⟨hc4, hz, hsq, h16⟩ := h
    refine ⟨?_, ?_, (sq_map_conj_iffK B m).1 hsq, ?_⟩
    · rw [← le_map_conj_hexaL_iffK hm]
      intro b hb
      exact (mem_hexaL_iff (sigma_le (hle hb))).2 (hz b hb)
    · rwa [card_map_conjK] at hc4
    · rwa [card_fixPts_map_conjK] at h16

end CFSG.KD.Hall82L
