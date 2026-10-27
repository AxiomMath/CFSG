module

public import CFSG.Certificates.Kernel.Hall82K.CodeSound
public import Certificates.Kernel.Hall82K.EnumGlue
public import Certificates.Kernel.Hall82K.Rm
public import Certificates.Kernel.Hall82K.Bridge
public import CFSG.CGT.Hall82.DModelFacts

public section

namespace CFSG.KD.Hall82R

open CFSG.KC.Hall82K CFSG.KC.Misc.Clos CFSG.KC.LQT CFSG.KC.Ord CFSG.KD.Hall82E CFSG.CGT.Hall82
open CFSG.ComponentClassification.AS81.Hexa CFSG.Monster.B.Co2

theorem impB_of {a b : Bool} (h : a = true → b = true) : P.impB a b = true := by
  cases a
  · rfl
  · exact h rfl

theorem andB_of {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  subst ha
  exact hb

theorem beqB_eq82 {a b : Bool} (h : beqB a b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · rfl

theorem memL_iff82 (z : ℕ) : ∀ L : List ℕ, memL z L = true ↔ z ∈ L
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => by simp at h⟩
  | h :: t => by
    change bor (Nat.beq z h) (memL z t) = true ↔ z ∈ h :: t
    rw [List.mem_cons, ← memL_iff82 z t]
    cases hb : Nat.beq z h
    · have hne : z ≠ h := fun e => by
        rw [e, Nat.beq_refl] at hb
        exact Bool.noConfusion hb
      simp only [bor, hne, false_or]
    · simp only [bor, Nat.eq_of_beq_eq_true hb, true_or]

theorem inU_iff (v : Fin 64) : InHallU v ↔ inUK v.val = true := by
  have h := beqB_eq82 ((allN_iff _ _).1 ch840003u0 v.val v.2)
  change v.val ∈ hallU0List ↔ _
  rw [← memL_iff82, h]

theorem bitN_eq82 (v j : ℕ) : bitN v j = if v.testBit j then 1 else 0 := by
  change (v >>> j) &&& 1 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]

def maskOf (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if p n then 2 ^ n else 0) + maskOf p n

theorem maskOf_lt (p : ℕ → Bool) : ∀ n, maskOf p n < 2 ^ n
  | 0 => by simp [maskOf]
  | n + 1 => by
    have := maskOf_lt p n
    rw [maskOf, pow_succ]
    split <;> omega

theorem testBit_maskOf (p : ℕ → Bool) : ∀ n, ∀ e < n, (maskOf p n).testBit e = p e
  | 0, e, he => absurd he (Nat.not_lt_zero e)
  | n + 1, e, he => by
    rw [maskOf]
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · split
      · rw [Nat.testBit_two_pow_add_gt he, testBit_maskOf p n e he]
      · rw [zero_add, testBit_maskOf p n e he]
    · split
      · rename_i hp
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (maskOf_lt p e), hp]
        rfl
      · rename_i hp
        rw [zero_add, Nat.testBit_lt_two_pow (maskOf_lt p e)]
        simpa using hp

theorem inM_maskOf (p : ℕ → Bool) {n e : ℕ} (he : e < n) : inM (maskOf p n) e = p e := by
  unfold inM
  rw [bitN_eq82, testBit_maskOf p n e he]
  cases p e <;> rfl

theorem zipArrK_getD : ∀ {L : List ℕ} {A : List (Array ℕ)}, zipArrK L A = true →
    ∀ i < L.length, codeArrK (L.getD i 0) (A.getD i #[]) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | c :: L, a :: A, h, i, hi => by
    have h' : band (codeArrK c a) (zipArrK L A) = true := h
    obtain ⟨h1, h2⟩ := band_eq_true82 h'
    cases i with
    | zero => exact h1
    | succ i => exact zipArrK_getD h2 i (by simpa using hi)

theorem basic_parts : rmC RMP 0 = idK ∧ ∀ e < 8, permK (rmC RMP e) = true ∧
    fix5K (rmC RMP e) = true ∧ ∀ f < 8, compL (rmC RMP e) (rmC RMP f) = rmC RMP (e ^^^ f) ∧
      (rmC RMP e = rmC RMP f → e = f) := by
  obtain ⟨h0, h1⟩ := andB_eq_true ch840003basic
  refine ⟨Nat.eq_of_beq_eq_true h0, fun e he => ?_⟩
  obtain ⟨hp, h2⟩ := andB_eq_true ((allN_iff _ _).1 h1 e he)
  obtain ⟨hf, h3⟩ := andB_eq_true h2
  refine ⟨hp, hf, fun f hf' => ?_⟩
  obtain ⟨hm, hi⟩ := andB_eq_true ((allN_iff _ _).1 h3 f hf')
  exact ⟨Nat.eq_of_beq_eq_true hm, fun h => Nat.eq_of_beq_eq_true
    (impB_eq_true hi (by rw [h]; exact Nat.beq_refl _))⟩

theorem rm_code (e : Fin 8) : hallRMPerm e ∈ addSub ∧ codeL (hallRMPerm e) = rmC RMP e.val := by
  have hz := zipArrK_getD ch840004br_rm e.val (e.2.trans_eq rfl)
  rw [← Nat.eq_of_beq_eq_true ((allN_iff _ _).1 ch840003rmK e.val e.2)] at hz
  obtain ⟨-, hm, hc, -⟩ := permK_sound (basic_parts.2 e.val e.2).1 hz
  exact ⟨hm, hc⟩

theorem rm_val (e : Fin 8) (v : Fin 64) : (hallRMPerm e v).val = apL (rmC RMP e.val) v.val := by
  rw [apL_code (rm_code e).1, (rm_code e).2]

theorem rm_zero : hallRMPerm 0 = 1 :=
  code_inj (rm_code 0).1 addSub.one_mem (by rw [(rm_code 0).2, codeL_one]; exact basic_parts.1)

theorem rm_mul (e f : Fin 8) : hallRMPerm e * hallRMPerm f = hallRMPerm (xor8 e f) := by
  obtain ⟨he, ce⟩ := rm_code e
  obtain ⟨hf, cf⟩ := rm_code f
  obtain ⟨hx, cx⟩ := rm_code (xor8 e f)
  refine code_inj (addSub.mul_mem he hf) hx ?_
  rw [codeL_mul he hf, ce, cf, cx]
  exact ((basic_parts.2 e.val e.2).2.2 f.val f.2).1

theorem rm_inv_self (e : Fin 8) : (hallRMPerm e)⁻¹ = hallRMPerm e := by
  have h := rm_mul e e
  have hx : xor8 e e = 0 := Fin.ext (by simp [xor8])
  rw [hx, rm_zero] at h
  exact inv_eq_of_mul_eq_one_right h

theorem rm_inj : Function.Injective hallRMPerm := by
  intro e f h
  have hc : rmC RMP e.val = rmC RMP f.val := by
    rw [← (rm_code e).2, ← (rm_code f).2, h]
  exact Fin.ext (((basic_parts.2 e.val e.2).2.2 f.val f.2).2 hc)

theorem mem_rm_iff (x : Equiv.Perm (Fin 64)) : x ∈ hallRM ↔ ∃ e, hallRMPerm e = x := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ e, hallRMPerm e = x) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨e, rfl⟩
      exact ⟨e, rfl⟩
    · exact ⟨0, rm_zero⟩
    · rintro x y _ _ ⟨e, rfl⟩ ⟨f, rfl⟩
      exact ⟨xor8 e f, (rm_mul e f).symm⟩
    · rintro x _ ⟨e, rfl⟩
      exact ⟨e, (rm_inv_self e).symm⟩
  · rintro ⟨e, rfl⟩
    exact Subgroup.subset_closure ⟨e, rfl⟩

theorem rm_le : hallRM ≤ hexaM := by
  change Subgroup.closure (Set.range hallRMPerm) ≤ hexaM
  rw [Subgroup.closure_le]
  rintro _ ⟨e, rfl⟩
  obtain ⟨he, ce⟩ := rm_code e
  have hI := (allN_iff _ _).1 ch840003mem e.val e.2
  simp only [letB_eq] at hI
  obtain ⟨hk, hEk⟩ := andB_eq_true hI
  obtain ⟨g, hg, hgc⟩ := hexaM_enum.2.2 _ (Nat.blt_eq.mp hk)
  have hge : g = hallRMPerm e := code_inj (hexaM_enum.2.1 g hg).1 he
    (by rw [hgc, ce]; exact Nat.eq_of_beq_eq_true hEk)
  exact hge ▸ hg

theorem rm_fix (e : Fin 8) : hallRMPerm e 5 = 5 := by
  apply Fin.ext
  rw [rm_val]
  exact Nat.eq_of_beq_eq_true (basic_parts.2 e.val e.2).2.1

theorem rm_not_le : ¬ hallRM ≤ hexaL := by
  intro hle
  have hmem : hallRMPerm 2 ∈ hexaL := hle (Subgroup.subset_closure ⟨2, rfl⟩)
  obtain ⟨-, k, hk, hc⟩ := hexaL_enum.2.1 _ hmem
  have h := negK_eq_true ((allN_iff _ _).1 ch840003notLe k hk)
  have ht : Nat.beq (EL k) (rmC RMP 2) = true := by
    rw [← hc, (rm_code 2).2]
    exact Nat.beq_refl _
  rw [ht] at h
  exact Bool.noConfusion h

theorem pow_two_dvd_sixteen82 {k : ℕ} (h : 2 ^ k ∣ 2160) : 2 ^ k ∣ 16 := by
  have h' : 2 ^ k ∣ 2 ^ 4 * 135 := by
    rw [show (2 : ℕ) ^ 4 * 135 = 2160 by norm_num]
    exact h
  exact (Nat.Coprime.pow_left k (by norm_num)).dvd_of_dvd_mul_right h'

theorem pow16_of_two {x : Equiv.Perm (Fin 64)} {X : Subgroup (Equiv.Perm (Fin 64))}
    (hX : X ≤ hexaM) (h2 : IsPGroup 2 X) (hx : x ∈ X) : x ^ 16 = 1 := by
  obtain ⟨n, hn⟩ := h2 ⟨x, hx⟩
  have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf x ∣ 2160 := by
    rw [← hexaM_enum.1]
    exact Subgroup.orderOf_dvd_natCard hexaM (hX hx)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn')
  have hdj : 2 ^ j ∣ 2160 := hj ▸ hdvd
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ pow_two_dvd_sixteen82 hdj)

theorem exists_hexaL_pair {w wi : ℕ} (hw : w < 1080) (hwi : wi < 1080)
    (hinv : compL (EL w) (EL wi) = idK) :
    ∃ a ∈ hexaL, a ∈ addSub ∧ codeL a = EL w ∧ codeL ⇑a⁻¹ = EL wi := by
  obtain ⟨a, ha, hac⟩ := hexaL_enum.2.2 w hw
  obtain ⟨b, hb, hbc⟩ := hexaL_enum.2.2 wi hwi
  have haA := (hexaL_enum.2.1 a ha).1
  have hbA := (hexaL_enum.2.1 b hb).1
  have hab : a * b = 1 := code_inj (addSub.mul_mem haA hbA) addSub.one_mem
    (by rw [codeL_mul haA hbA, hac, hbc, hinv]; rfl)
  refine ⟨a, ha, haA, hac, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hab, hbc]

theorem fix5_of {a : Equiv.Perm (Fin 64)} (ha : a ∈ addSub) (h : fix5K (codeL a) = true) :
    a 5 = 5 :=
  Fin.ext ((apL_code ha 5).trans (Nat.eq_of_beq_eq_true h))

theorem le_rm (B : Subgroup (Equiv.Perm (Fin 64))) (hB : B ≤ hexaM)
    (h2 : IsPGroup 2 B) (hfix : ∀ b ∈ B, b 5 = 5)
    (hnorm : ∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) : B ≤ hallRM := by
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1, ← rm_zero]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  obtain ⟨hbA, k, hk, hbk⟩ := hexaM_enum.2.1 b (hB hb)
  have hchk := (allN_iff _ _).1 ch840003nv k hk
  simp only [nvAtK, letB_eq] at hchk
  rw [← hbk] at hchk
  have e5 : apL (codeL b) 5 = 5 := by
    have h := apL_code hbA 5
    rw [hfix b hb] at h
    exact h.symm
  have h5 : fix5K (codeL b) = true := by
    unfold fix5K
    rw [e5]
    rfl
  have hne : negK (Nat.beq (codeL b) idK) = true := by
    cases h : Nat.beq (codeL b) idK
    · rfl
    · exact absurd (code_inj hbA addSub.one_mem (Nat.eq_of_beq_eq_true h)) hb1
  have h16 : Nat.beq (powL (codeL b) 16) idK = true := by
    rw [← codeL_pow hbA, pow16_of_two hB h2 hb, codeL_one]
    exact Nat.beq_refl _
  have hres := impB_eq_true hchk (by rw [h5, hne, h16]; rfl)
  rcases orB_eq_true82 hres with hr | hw
  · obtain ⟨e, he, hbe⟩ := (anyN_iff _ _).1 hr
    have hbeq : b = hallRMPerm ⟨e, he⟩ := code_inj hbA (rm_code _).1
      (by rw [(rm_code _).2]; exact Nat.eq_of_beq_eq_true hbe)
    rw [hbeq]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  · exfalso
    simp only [nvWitK, letB_eq] at hw
    obtain ⟨hw1, hw⟩ := andB_eq_true hw
    obtain ⟨hw2, hw⟩ := andB_eq_true hw
    obtain ⟨hw3, hw⟩ := andB_eq_true hw
    obtain ⟨hw4, hw5⟩ := andB_eq_true hw
    obtain ⟨a, haL, haA, hac, haic⟩ :=
      exists_hexaL_pair (Nat.blt_eq.mp hw1) (Nat.blt_eq.mp hw2) (Nat.eq_of_beq_eq_true hw4)
    have ha5 : a 5 = 5 := fix5_of haA (hac ▸ hw3)
    have hz : a * b * a⁻¹ ∈ B := hnorm a haL ha5 b hb
    have hq : b * (a * b * a⁻¹) ^ 15 ∈ B := B.mul_mem hb (B.pow_mem hz 15)
    have hq16 := pow16_of_two hB h2 hq
    have hzA : a * b * a⁻¹ ∈ addSub :=
      addSub.mul_mem (addSub.mul_mem haA hbA) (addSub.inv_mem haA)
    have hqA : b * (a * b * a⁻¹) ^ 15 ∈ addSub := addSub.mul_mem hbA (addSub.pow_mem hzA 15)
    have hcode := codeL_pow hqA 16
    rw [hq16, codeL_one, codeL_mul hbA (addSub.pow_mem hzA 15), codeL_pow hzA,
      codeL_mul (addSub.mul_mem haA hbA) (addSub.inv_mem haA), codeL_mul haA hbA, hac,
      haic] at hcode
    have h := negK_eq_true hw5
    rw [← hcode, Nat.beq_refl] at h
    exact Bool.noConfusion h

theorem u_inv : ∀ s ∈ hexaM, s 5 = 5 → ∀ v, InHallU v → InHallU (s v) := by
  intro s hs hs5 v hv
  obtain ⟨hsA, k, hk, hsk⟩ := hexaM_enum.2.1 s hs
  have hchk := (allN_iff _ _).1 ch840003uInv k hk
  simp only [uInvAtK, letB_eq] at hchk
  rw [← hsk] at hchk
  have e5 : apL (codeL s) 5 = 5 := by
    have h := apL_code hsA 5
    rw [hs5] at h
    exact h.symm
  have h5 : fix5K (codeL s) = true := by
    unfold fix5K
    rw [e5]
    rfl
  have hall := (allN_iff _ _).1 (impB_eq_true hchk h5) v.val v.2
  rw [inU_iff, apL_code hsA]
  exact impB_eq_true hall ((inU_iff v).1 hv)

theorem rm_comm_u (e : Fin 8) (v : Fin 64) (hv : InHallU v) :
    xorF (hallRMPerm e v) v = 0 ∨ xorF (hallRMPerm e v) v = 5 := by
  have h := (andB_eq_true ((allN_iff _ _).1 ch840003rmU e.val e.2)).1
  have h' := impB_eq_true ((allN_iff _ _).1 h v.val v.2) ((inU_iff v).1 hv)
  simp only [letB_eq] at h'
  have hval : (xorF (hallRMPerm e v) v).val = Nat.xor (apL (rmC RMP e.val) v.val) v.val := by
    rw [val_xorF, rm_val]
    rfl
  rcases orB_eq_true82 h' with h0 | h5
  · exact Or.inl (Fin.ext (hval.trans (Nat.eq_of_beq_eq_true h0)))
  · exact Or.inr (Fin.ext (hval.trans (Nat.eq_of_beq_eq_true h5)))

theorem rm_eq_zero_of_fix_u (e : Fin 8) (hfix : ∀ v, InHallU v → hallRMPerm e v = v) :
    e = 0 := by
  have h := (andB_eq_true ((allN_iff _ _).1 ch840003rmU e.val e.2)).2
  rcases orB_eq_true82 h with h0 | hu
  · exact Fin.ext (Nat.eq_of_beq_eq_true h0)
  · exfalso
    obtain ⟨u, hu64, hu⟩ := (anyN_iff _ _).1 hu
    obtain ⟨huU, hmv⟩ := andB_eq_true hu
    have hf := hfix ⟨u, hu64⟩ ((inU_iff ⟨u, hu64⟩).2 huU)
    have hv := rm_val e ⟨u, hu64⟩
    rw [hf] at hv
    have h' := negK_eq_true hmv
    rw [← hv, Nat.beq_refl] at h'
    exact Bool.noConfusion h'

theorem fix_rm (v : Fin 64) (hfix : ∀ e, hallRMPerm e v = v) : v = 0 ∨ v = 5 := by
  have h := (allN_iff _ _).1 ch840003fix v.val v.2
  rcases orB_eq_true82 h with h05 | he
  · rcases orB_eq_true82 h05 with h0 | h5
    · exact Or.inl (Fin.ext (Nat.eq_of_beq_eq_true h0))
    · exact Or.inr (Fin.ext (Nat.eq_of_beq_eq_true h5))
  · exfalso
    obtain ⟨e, he8, hm⟩ := (anyN_iff _ _).1 he
    have hv := rm_val ⟨e, he8⟩ v
    rw [hfix] at hv
    have h' := negK_eq_true hm
    rw [← hv, Nat.beq_refl] at h'
    exact Bool.noConfusion h'

theorem rm_le_or_quad (B : Subgroup (Equiv.Perm (Fin 64))) (hB : B ≤ hallRM)
    (hnorm : ∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    hallRM ≤ B ∨ ∀ a ∈ B, ∀ b ∈ B, ∀ v,
      xorF (xorF (a (b v)) (a v)) (xorF (b v) v) = 0 := by
  classical
  let p : ℕ → Bool := fun e => if h : e < 8 then decide (hallRMPerm ⟨e, h⟩ ∈ B) else false
  let m := maskOf p 8
  have hm : ∀ e : Fin 8, inM m e.val = true ↔ hallRMPerm e ∈ B := by
    intro e
    rw [inM_maskOf p e.2]
    simp [p, e.2]
  have hm' : ∀ e (he : e < 8), inM m e = true ↔ hallRMPerm ⟨e, he⟩ ∈ B := fun e he =>
    hm ⟨e, he⟩
  have hm256 : m < 256 := maskOf_lt p 8
  have hclosed : closed8K m = true := by
    refine (allN_iff _ _).2 fun e he => (allN_iff _ _).2 fun f hf => impB_of fun hef => ?_
    obtain ⟨hme, hmf⟩ := andB_eq_true hef
    have hx : Nat.xor e f < 8 := Nat.xor_lt_two_pow (n := 3) he hf
    rw [hm' _ hx]
    have h := B.mul_mem ((hm' e he).1 hme) ((hm' f hf).1 hmf)
    rw [rm_mul] at h
    exact h
  have hchk := impB_eq_true ((allN_iff _ _).1 ch840003sub m hm256) hclosed
  rcases orB_eq_true82 hchk with hall | hrest
  · left
    intro x hx
    obtain ⟨e, rfl⟩ := (mem_rm_iff x).1 hx
    refine (hm e).1 ?_
    have h255 : m = 255 := Nat.eq_of_beq_eq_true hall
    rw [h255]
    have h8 : ∀ e : Fin 8, inM 255 e.val = true := by decide
    exact h8 e
  rcases orB_eq_true82 hrest with hquad | hwit
  · right
    intro a ha b hb v
    obtain ⟨e, rfl⟩ := (mem_rm_iff a).1 (hB ha)
    obtain ⟨f, rfl⟩ := (mem_rm_iff b).1 (hB hb)
    have h := impB_eq_true ((allN_iff _ _).1 ((allN_iff _ _).1 hquad e.val e.2) f.val f.2)
      (andB_of ((hm e).2 ha) ((hm f).2 hb))
    have hv := Nat.eq_of_beq_eq_true ((allN_iff _ _).1 h v.val v.2)
    apply Fin.ext
    simp only [val_xorF]
    rw [rm_val e, rm_val e, rm_val f]
    exact hv
  · exfalso
    simp only [subWitK, letB_eq] at hwit
    obtain ⟨hw1, hw⟩ := andB_eq_true hwit
    obtain ⟨hw2, hw⟩ := andB_eq_true hw
    obtain ⟨hw3, hw⟩ := andB_eq_true hw
    obtain ⟨hw4, hw⟩ := andB_eq_true hw
    obtain ⟨hw5, hw⟩ := andB_eq_true hw
    obtain ⟨hw6, hw⟩ := andB_eq_true hw
    obtain ⟨hw7, hw8⟩ := andB_eq_true hw
    obtain ⟨a, haL, haA, hac, haic⟩ :=
      exists_hexaL_pair (Nat.blt_eq.mp hw1) (Nat.blt_eq.mp hw2) (Nat.eq_of_beq_eq_true hw4)
    have ha5 : a 5 = 5 := fix5_of haA (hac ▸ hw3)
    have he8 : Nat.land (Nat.shiftRight (lane SW 32 4294967295 m) 22) 7 < 8 :=
      Nat.lt_succ_of_le Nat.and_le_right
    have hf8 := Nat.blt_eq.mp hw6
    have heB := (hm' _ he8).1 hw5
    have hconj := hnorm a haL ha5 _ heB
    have heq : a * hallRMPerm ⟨_, he8⟩ * a⁻¹ = hallRMPerm ⟨_, hf8⟩ := by
      obtain ⟨heA, hec⟩ := rm_code ⟨_, he8⟩
      obtain ⟨hfA, hfc⟩ := rm_code ⟨_, hf8⟩
      refine code_inj (addSub.mul_mem (addSub.mul_mem haA heA) (addSub.inv_mem haA)) hfA ?_
      rw [codeL_mul (addSub.mul_mem haA heA) (addSub.inv_mem haA), codeL_mul haA heA, hac,
        haic, hec, hfc]
      exact Nat.eq_of_beq_eq_true hw8
    rw [heq] at hconj
    have h := negK_eq_true hw7
    rw [(hm' _ hf8).2 hconj] at h
    exact Bool.noConfusion h

theorem u_maximal (W : Set (Fin 64)) (hW : ∀ v ∈ W, ∀ w ∈ W, xorF v w ∈ W)
    (hU : ∀ v, InHallU v → v ∈ W)
    (hInv : ∀ a ∈ hexaL, a 5 = 5 → ∀ w ∈ W, a w ∈ W) :
    W = {v | InHallU v} ∨ W = Set.univ := by
  classical
  by_cases hex : ∃ a : Fin 64, ¬ InHallU a ∧ a ∈ W
  · right
    obtain ⟨a, haU, haW⟩ := hex
    have hna : negK (inUK a.val) = true := by
      cases h : inUK a.val
      · rfl
      · exact absurd ((inU_iff a).2 h) haU
    have hchk := impB_eq_true ((allN_iff _ _).1 ch840003uMax a.val a.2) hna
    simp only [letB_eq] at hchk
    obtain ⟨hw1, hw⟩ := andB_eq_true hchk
    obtain ⟨hw2, hw⟩ := andB_eq_true hw
    obtain ⟨-, hw⟩ := andB_eq_true hw
    obtain ⟨-, hall⟩ := andB_eq_true hw
    obtain ⟨g, hgL, hgc⟩ := hexaL_enum.2.2 _ (Nat.blt_eq.mp hw1)
    have hgA := (hexaL_enum.2.1 g hgL).1
    have hg5 : g 5 = 5 := fix5_of hgA (hgc ▸ hw2)
    set b := g a with hb
    have hbv : b.val = apL (EL (lane UMW 11 2047 a.val)) a.val := by
      rw [hb, apL_code hgA, hgc]
    have hbW : b ∈ W := hInv g hgL hg5 a haW
    have hbaW : xorF b a ∈ W := hW b hbW a haW
    have hUv : ∀ u : ℕ, inUK u = true → ∀ hu : u < 64, (⟨u, hu⟩ : Fin 64) ∈ W :=
      fun u h hu => hU ⟨u, hu⟩ ((inU_iff ⟨u, hu⟩).2 h)
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx := (allN_iff _ _).1 hall x.val x.2
    rw [← hbv] at hx
    rcases orB_eq_true82 hx with hx01 | hx23
    · rcases orB_eq_true82 hx01 with hx0 | hx1
      · exact hUv _ hx0 x.2
      · have hu := hUv _ hx1 (Nat.xor_lt_two_pow (n := 6) x.2 a.2)
        have hux : xorF ⟨Nat.xor x.val a.val, Nat.xor_lt_two_pow (n := 6) x.2 a.2⟩ a = x :=
          Fin.ext (by simp [xorF, Nat.xor_assoc])
        rw [← hux]
        exact hW _ hu a haW
    · rcases orB_eq_true82 hx23 with hx2 | hx3
      · have hlt : Nat.xor x.val (Nat.xor b.val a.val) < 64 :=
          Nat.xor_lt_two_pow (n := 6) x.2 (Nat.xor_lt_two_pow (n := 6) b.2 a.2)
        have hu := hUv _ hx2 hlt
        have hux : xorF ⟨_, hlt⟩ (xorF b a) = x := Fin.ext (by simp [xorF, Nat.xor_assoc])
        rw [← hux]
        exact hW _ hu _ hbaW
      · have hlt : Nat.xor x.val b.val < 64 := Nat.xor_lt_two_pow (n := 6) x.2 b.2
        have hu := hUv _ hx3 hlt
        have hux : xorF ⟨_, hlt⟩ b = x := Fin.ext (by simp [xorF, Nat.xor_assoc])
        rw [← hux]
        exact hW _ hu b hbW
  · left
    ext x
    constructor
    · intro hxW
      by_contra hxU
      exact hex ⟨x, hxU, hxW⟩
    · intro hx
      exact hU x hx

end CFSG.KD.Hall82R
