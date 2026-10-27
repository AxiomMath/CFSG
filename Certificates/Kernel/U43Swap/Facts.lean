module

public import Certificates.Kernel.U43Swap.Checks
public import Certificates.Kernel.U43Swap.Bits
public import Certificates.Kernel.U43Mod.Glue
public import CFSG.Certificates.Kernel.U43Swap.Group

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Swap

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Swap CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CertificateChecks.KernelU43Mod

abbrev G820 : Type := Equiv.Perm (Fin 820)

theorem strictB_elim {y : ℕ} {k : ℕ → Bool} (h : CFSG.KC.Enum.strictB y k = true) :
    k y = true := by
  rwa [CFSG.KS.U43Mod.strictB_eq] at h

theorem bIf_cases {c a b : Bool} (h : Bool.rec (motive := fun _ => Bool) b a c = true) :
    (c = true ∧ a = true) ∨ (c = false ∧ b = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem nIf_true {c : Bool} {a b : ℕ} (h : c = true) : Bool.rec (motive := fun _ => ℕ) b a c = a := by
  subst h
  rfl

theorem nIf_false {c : Bool} {a b : ℕ} (h : c = false) :
    Bool.rec (motive := fun _ => ℕ) b a c = b := by
  subst h
  rfl

theorem blt_lt {a b : ℕ} (h : Nat.blt a b = true) : a < b := Nat.blt_eq.mp h

theorem land_lt {x m : ℕ} : Nat.land x m < m + 1 := Nat.lt_succ_of_le Nat.and_le_right

theorem fld0 (k : ℕ) : (k >>> 0) &&& 1023 = k % 1024 := by
  rw [Nat.shiftRight_zero]
  exact Nat.and_two_pow_sub_one_eq_mod k 10

theorem fld10 (k : ℕ) : (k >>> 10) &&& 1023 = k / 1024 % 1024 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 10

theorem fld20 (k : ℕ) : (k >>> 20) &&& 1023 = k / 1048576 % 1024 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 10

theorem keyOK_iff {k : ℕ} {f : ℕ → ℕ} :
    keyOK k f = true ↔ k % 1024 = f 0 ∧ k / 1024 % 1024 = f 1 ∧ k / 1048576 % 1024 = f 9 := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq ((k >>> 20) &&& 1023) (f 9))
      (Nat.beq ((k >>> 10) &&& 1023) (f 1))) (Nat.beq ((k >>> 0) &&& 1023) (f 0)) = true ↔ _
  rw [bAnd_iff, bAnd_iff, beq_iff, beq_iff, beq_iff, fld0, fld10, fld20]

theorem eqB_iff {f g : ℕ → ℕ} : eqB f g = true ↔ f 0 = g 0 ∧ f 1 = g 1 ∧ f 9 = g 9 := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq (f 9) (g 9)) (Nat.beq (f 1) (g 1)))
      (Nat.beq (f 0) (g 0)) = true ↔ _
  rw [bAnd_iff, bAnd_iff, beq_iff, beq_iff, beq_iff]

theorem bpt_lt (p : ℕ) : bpt p < 820 := by
  have key : ∀ b c : Bool, Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 9 1 c)
      0 b < 820 := by decide
  exact key _ _

theorem inj_of_lt {v : ℕ → ℕ} {n : ℕ} (h : ∀ i, 0 < i → i < n → v (i - 1) < v i) :
    ∀ i < n, ∀ j < n, v i = v j → i = j := by
  have mono : ∀ i j, i < j → j < n → v i < v j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := h (j + 1) (by omega) hj
      rw [Nat.add_sub_cancel] at hs
      rcases Nat.lt_or_ge i j with hl | hl
      · exact (ih hl (by omega)).trans hs
      · have : i = j := by omega
        subst this
        exact hs
  intro i hi j hj e
  rcases Nat.lt_trichotomy i j with hl | hl | hl
  · exact absurd e (mono i j hl hj).ne
  · exact hl
  · exact absurd e (mono j i hl hi).ne'

@[expose] def PM (f : ℕ → ℕ) (x : G820) : Prop := ∀ q (hq : q < 820), f q = (x ⟨q, hq⟩ : ℕ)

theorem PM.congr {f : ℕ → ℕ} {x y : G820} (h : PM f x) (e : x = y) : PM f y := e ▸ h

theorem pm_comp {f g : ℕ → ℕ} {x y : G820} (hf : PM f x) (hg : PM g y) :
    PM (fun q => f (g q)) (x * y) := fun q hq => by
  change f (g q) = _
  rw [hg q hq, hf _ (Fin.is_lt _), Fin.eta, Equiv.Perm.mul_apply]

theorem pm_fpow {f : ℕ → ℕ} {x : G820} (hf : PM f x) : ∀ o, PM (fpow f o) (x ^ o)
  | 0, q, hq => by
    rw [pow_zero]
    rfl
  | o + 1, q, hq => by
    change strictN (f q) (fpow f o) = _
    rw [CFSG.KS.U43Mod.strictN_eq, hf q hq, pm_fpow hf o _ (Fin.is_lt _), Fin.eta, pow_succ,
      Equiv.Perm.mul_apply]

theorem eq_of_keys {k : ℕ} {f g : ℕ → ℕ} {x y : G820}
    (hf : PM f x) (hg : PM g y) (hx : x ∈ P) (hy : y ∈ P) (h1 : keyOK k f = true)
    (h2 : keyOK k g = true) : x = y := by
  rw [keyOK_iff] at h1 h2
  refine eq_of_base hx hy fun p hp => Fin.ext ?_
  rw [← hf, ← hg]
  simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h1.1.symm.trans h2.1
  · exact h1.2.1.symm.trans h2.2.1
  · exact h1.2.2.symm.trans h2.2.2

theorem comm_of_cmB {f g : ℕ → ℕ} {x y : G820} (hf : PM f x)
    (hg : PM g y) (hx : x ∈ P) (hy : y ∈ P) (h : cmB f g = true) : x * y = y * x := by
  have h' := eqB_iff.1 h
  refine eq_of_base (P.mul_mem hx hy) (P.mul_mem hy hx) fun p hp => Fin.ext ?_
  rw [← pm_comp hf hg, ← pm_comp hg hf]
  simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h'.1
  · exact h'.2.1
  · exact h'.2.2

theorem ne_of_ncw {f g : ℕ → ℕ} {x y : G820} {p : ℕ} (hf : PM f x) (hg : PM g y)
    (h : ncw f g p = true) : x * y ≠ y * x := by
  intro e
  have hc := (bIf_cases (strictB_elim h))
  have hb := bpt_lt p
  have heq : f (g (bpt p)) = g (f (bpt p)) := by
    rw [hg _ hb, hf _ (Fin.is_lt _), hf _ hb, hg _ (Fin.is_lt _), Fin.eta, Fin.eta,
      ← Equiv.Perm.mul_apply, e, Equiv.Perm.mul_apply]
  rcases hc with ⟨-, hc⟩ | ⟨hc, -⟩
  · exact Bool.false_ne_true hc
  · exact Nat.ne_of_beq_eq_false hc heq

@[expose] noncomputable def LE (e : ℕ) : G820 := if e < 4 then m5 e else (m5 (e - 4))⁻¹

@[expose] noncomputable def TP (e : ℕ) : G820 := permOfArr 820 (unpack 820 10 (PT e))

theorem kP_spec {e : ℕ} (he : e < 4) :
    permOK 820 10 (mask 10) (820 * 10) (PT e) (PT (e + 4)) = true ∧ inPU (PT e) = true ∧
      baseEq bs (pg 10 (mask 10) (PT e)) (GM e) = true := by
  have h := allN_spec kP e he
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨h1, h2, h3⟩

theorem rep_TP {e : ℕ} (he : e < 4) :
    Rep 820 (unpack 820 10 (PT e)) (TP e) ∧ Rep 820 (unpack 820 10 (PT (e + 4))) (TP e)⁻¹ :=
  rep_permOfArr (isInvA_unpack (kP_spec he).1)

theorem TP_pt {e : ℕ} (he : e < 4) (q : ℕ) (hq : q < 820) :
    pg 10 (mask 10) (PT e) q = (TP e ⟨q, hq⟩ : ℕ) := by
  rw [← unpack_get hq]
  exact (rep_TP he).1 ⟨q, hq⟩

theorem TPi_pt {e : ℕ} (he : e < 4) (q : ℕ) (hq : q < 820) :
    pg 10 (mask 10) (PT (e + 4)) q = ((TP e)⁻¹ ⟨q, hq⟩ : ℕ) := by
  rw [← unpack_get hq]
  exact (rep_TP he).2 ⟨q, hq⟩

theorem TP_mem {e : ℕ} (he : e < 4) : TP e ∈ P := by
  have hr : allN 820 (fun i => Nat.blt (pg 10 (mask 10) (PT e) i) 820) = true :=
    CFSG.KS.PackFld.allN_of_forall fun i hi => by
      rw [← unpack_get hi]
      exact Nat.blt_eq.mpr ((rep_TP he).1.lt hi)
  have hs := siftK_sound binds perm C.hl rfl hr (kP_spec he).2.1
  rw [← base_eq] at hs
  exact (inP_iff (rep_TP he).1).1 hs

theorem TP_eq {e : ℕ} (he : e < 4) : TP e = m5 e :=
  eq_of_baseEq (TP_mem he) (m5_mem e) (TP_pt he) (GM_eq e) (kP_spec he).2.2

theorem pm_lp {e : ℕ} (he : e < 8) : PM (lp PT e) (LE e) := fun q hq => by
  change pg 10 (mask 10) (PT e) q = _
  rcases Nat.lt_or_ge e 4 with h | h
  · rw [LE, if_pos h, ← TP_eq h]
    exact TP_pt h q hq
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 := ⟨e - 4, by omega⟩
    rw [LE, if_neg (by omega), Nat.add_sub_cancel, ← TP_eq (by omega)]
    exact TPi_pt (by omega) q hq

theorem LE_xor {l : ℕ} (hl : l < 8) : LE (Nat.xor l 4) = (LE l)⁻¹ := by
  have hx : Nat.xor l 4 = if l < 4 then l + 4 else l - 4 := by interval_cases l <;> rfl
  rw [hx]
  split_ifs with h
  · simp [LE, h]
  · simp [LE, h, show l - 4 < 4 by omega]

theorem xor_lt {l : ℕ} (hl : l < 8) : Nat.xor l 4 < 8 := by interval_cases l <;> decide

theorem m5_mem_H4 {e : ℕ} (he : e < 4) : m5 e ∈ H4 := m4_eq he ▸ m4_mem_H4 he

theorem LE_mem {e : ℕ} (he : e < 8) : LE e ∈ H4 := by
  unfold LE
  split_ifs with h
  · exact m5_mem_H4 h
  · exact H4.inv_mem (m5_mem_H4 (by omega))

theorem memP {x : G820} (hx : x ∈ H4) : x ∈ P := H4_le_P hx

@[expose] noncomputable def wval (W : ℕ) : ℕ → G820
  | 0 => 1
  | k + 1 => wval W k * LE fld(W, Nat.mul (nat_lit 3) k, nat_lit 7)

theorem pm_wp (W : ℕ) : ∀ n, PM (wp PT W n) (wval W n)
  | 0, q, hq => rfl
  | n + 1, q, hq => by
    change strictN (lp PT fld(W, Nat.mul (nat_lit 3) n, nat_lit 7) q) (wp PT W n) = _
    rw [CFSG.KS.U43Mod.strictN_eq, pm_lp land_lt q hq, pm_wp W n _ (Fin.is_lt _), Fin.eta, wval,
      Equiv.Perm.mul_apply]

theorem pm_wpI (W : ℕ) : ∀ n, PM (wpI PT W n) (wval W n)⁻¹
  | 0, q, hq => by
    change q = _
    simp [wval]
  | n + 1, q, hq => by
    change strictN (wpI PT W n q)
      (lp PT (Nat.xor fld(W, Nat.mul (nat_lit 3) n, nat_lit 7) (nat_lit 4))) = _
    rw [CFSG.KS.U43Mod.strictN_eq, pm_wpI W n q hq, pm_lp (xor_lt land_lt) _ (Fin.is_lt _), LE_xor land_lt,
      Fin.eta, wval, mul_inv_rev, Equiv.Perm.mul_apply]

theorem wval_mem (W : ℕ) : ∀ n, wval W n ∈ H4
  | 0 => H4.one_mem
  | n + 1 => H4.mul_mem (wval_mem W n) (LE_mem land_lt)

@[expose] noncomputable def s0 : G820 := m5 1

@[expose] noncomputable def u0 : G820 := m5 2

@[expose] noncomputable def t0 : G820 := evalG m5 sig2W

theorem t0_eq : t0 = u0⁻¹ * s0 * u0 := by
  simp only [t0, u0, s0, evalG, sig2W, List.map, letterVal, List.prod_cons, List.prod_nil,
    if_true, Bool.false_eq_true, ↓reduceIte, mul_one, mul_assoc]

@[expose] noncomputable def y9 (e : ℕ) : G820 := CFSG.KS.U43Swap.yE s0 t0 e

theorem conj_pow' (u s : G820) (n : ℕ) : (u⁻¹ * s * u) ^ n = u⁻¹ * s ^ n * u := by
  have := conj_pow (a := u⁻¹) (b := s) (i := n)
  simpa using this

theorem y9_eq (e : ℕ) : y9 e = s0 ^ (e % 3) * (u0⁻¹ * (s0 ^ (e / 3) * u0)) := by
  rw [y9, CFSG.KS.U43Swap.yE, t0_eq, conj_pow']
  group

theorem pm_sp (e : ℕ) : PM (sp PT e) (y9 e) := by
  have h := pm_comp (pm_fpow (pm_lp (e := 1) (by norm_num)) (e % 3))
    (pm_comp (pm_lp (e := 6) (by norm_num))
      (pm_comp (pm_fpow (pm_lp (e := 1) (by norm_num)) (e / 3)) (pm_lp (e := 2) (by norm_num))))
  have hf : sp PT e = fun q => fpow (lp PT 1) (e % 3) (lp PT 6 (fpow (lp PT 1) (e / 3)
      (lp PT 2 q))) := by
    funext q
    simp only [sp, CFSG.KS.U43Mod.strictN_eq] <;> rfl
  rw [hf]
  refine h.congr ?_
  rw [y9_eq]
  simp [LE, s0, u0]

theorem pm_spI (e : ℕ) : PM (spI PT e) (y9 e)⁻¹ := by
  have h := pm_comp (pm_lp (e := 6) (by norm_num))
    (pm_comp (pm_fpow (pm_lp (e := 5) (by norm_num)) (e / 3))
      (pm_comp (pm_lp (e := 2) (by norm_num)) (pm_fpow (pm_lp (e := 5) (by norm_num)) (e % 3))))
  have hf : spI PT e = fun q => lp PT 6 (fpow (lp PT 5) (e / 3) (lp PT 2
      (fpow (lp PT 5) (e % 3) q))) := by
    funext q
    simp only [spI, CFSG.KS.U43Mod.strictN_eq] <;> rfl
  rw [hf]
  refine h.congr ?_
  rw [y9_eq]
  simp only [LE, s0, u0]
  norm_num
  group

@[expose] noncomputable def wd (r : ℕ) : G820 := wval r (rl r)

@[expose] noncomputable def cE (r e : ℕ) : G820 := wd r * y9 e * (wd r)⁻¹

theorem pm_cp (r e : ℕ) : PM (cp PT r e) (cE r e) := by
  have h := pm_comp (pm_wp r (rl r)) (pm_comp (pm_sp e) (pm_wpI r (rl r)))
  have hf : cp PT r e = fun q => wp PT r (rl r) (sp PT e (wpI PT r (rl r) q)) := by
    funext q
    simp only [cp, CFSG.KS.U43Mod.strictN_eq] <;> rfl
  rw [hf]
  exact h.congr (by rw [cE, wd, mul_assoc])

theorem pm_cpI (r e : ℕ) : PM (cpI PT r e) (cE r e)⁻¹ := by
  have h := pm_comp (pm_wp r (rl r)) (pm_comp (pm_spI e) (pm_wpI r (rl r)))
  have hf : cpI PT r e = fun q => wp PT r (rl r) (spI PT e (wpI PT r (rl r) q)) := by
    funext q
    simp only [cpI, CFSG.KS.U43Mod.strictN_eq] <;> rfl
  rw [hf]
  exact h.congr (by rw [cE, wd]; group)

@[expose] noncomputable def xE (r : ℕ) : G820 := cE r (oE r)

theorem pm_oEl (r : ℕ) : PM (oEl PT r) (xE r) := pm_cp r (oE r)

theorem pm_oElI (r : ℕ) : PM (oElI PT r) (xE r)⁻¹ := pm_cpI r (oE r)

theorem pm_oConj (r : ℕ) {f : ℕ → ℕ} {x : G820} (hf : PM f x) :
    PM (oConj PT r f) (xE r * x * (xE r)⁻¹) := by
  have h := pm_comp (pm_oEl r) (pm_comp hf (pm_oElI r))
  have hf' : oConj PT r f = fun q => oEl PT r (f (oElI PT r q)) := by
    funext q
    simp only [oConj, CFSG.KS.U43Mod.strictN_eq] <;> rfl
  rw [hf']
  exact h.congr (by rw [mul_assoc])

@[expose] noncomputable def Yv (k : ℕ) : G820 := cE (YR k) (CFSG.KC.U43Swap.yE k)

theorem pm_yEl (k : ℕ) : PM (yEl PT YR k) (Yv k) := pm_cp (YR k) _

theorem s0_mem : s0 ∈ H4 := m5_mem_H4 (by norm_num)

theorem u0_mem : u0 ∈ H4 := m5_mem_H4 (by norm_num)

theorem t0_mem : t0 ∈ H4 := by
  rw [t0_eq]
  exact H4.mul_mem (H4.mul_mem (H4.inv_mem u0_mem) s0_mem) u0_mem

theorem y9_mem (e : ℕ) : y9 e ∈ H4 :=
  H4.mul_mem (H4.pow_mem s0_mem _) (H4.pow_mem t0_mem _)

theorem cE_mem (r e : ℕ) : cE r e ∈ H4 :=
  H4.mul_mem (H4.mul_mem (wval_mem _ _) (y9_mem e)) (H4.inv_mem (wval_mem _ _))

theorem yEk (k : ℕ) : CFSG.KC.U43Swap.yE k = if k < 4 then 1 else 3 := by
  split_ifs with h
  · exact nIf_true (Nat.blt_eq.mpr h)
  · exact nIf_false (Bool.eq_false_iff.2 fun h' => h (Nat.blt_eq.mp h'))

theorem y9_one : y9 1 = s0 := by simp [y9, CFSG.KS.U43Swap.yE]

theorem y9_three : y9 3 = t0 := by simp [y9, CFSG.KS.U43Swap.yE]

theorem pm_id : PM (fun q => q) 1 := fun _ _ => rfl

theorem eq_of_eqB {f g : ℕ → ℕ} {x y : G820} (hf : PM f x) (hg : PM g y) (hx : x ∈ P)
    (hy : y ∈ P) (h : eqB f g = true) : x = y := by
  have h' := eqB_iff.1 h
  refine eq_of_base hx hy fun p hp => Fin.ext ?_
  rw [← hf, ← hg]
  simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact h'.1
  · exact h'.2.1
  · exact h'.2.2

theorem oKey_spec {i : ℕ} (hi : i < 81) : keyOK (oK (OD i)) (oEl PT (OD i)) = true :=
  ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (strictB_elim (allN_spec kOKey i hi))).2).2

theorem key_X {c : ℕ} (hc : c < 81) {f : ℕ → ℕ} {x : G820} (hf : PM f x) (hx : x ∈ H4)
    (h : keyOK (oK (OD c)) f = true) : xE (OD c) = x :=
  eq_of_keys (pm_oEl _) hf (memP (cE_mem _ _)) (memP hx) (oKey_spec hc) h

theorem yRec_spec {k : ℕ} (hk : k < 8) :
    keyOK (YR k >>> 28) (cp PT (YR k) (CFSG.KC.U43Swap.yE k)) = true ∧
      ∃ o < 81, keyOK (YR k >>> 28) (oConj PT (OD o) (sp PT (CFSG.KC.U43Swap.yE k))) = true := by
  have h := (bAnd_iff _ _).1 (strictB_elim (allN_spec kY k hk))
  have h2 := (bAnd_iff _ _).1 (strictB_elim h.2)
  exact ⟨h.1, _, blt_lt h2.1, h2.2⟩

theorem key_Y {k : ℕ} (hk : k < 8) {f : ℕ → ℕ} {x : G820} (hf : PM f x) (hx : x ∈ H4)
    (h : keyOK (YR k >>> 28) f = true) : x = Yv k :=
  eq_of_keys hf (pm_yEl k) (memP hx) (memP (cE_mem _ _)) h (yRec_spec hk).1

theorem conj_mem {c x : G820} (hc : c ∈ H4) (hx : x ∈ H4) : c * x * c⁻¹ ∈ H4 :=
  H4.mul_mem (H4.mul_mem hc hx) (H4.inv_mem hc)

theorem t2d_spec {r t h c : ℕ} (H : t2d PT YR r t h c = true) :
    (∃ k < 4, xE r * Yv (h + k) ≠ Yv (h + k) * xE r) ∨
      ∀ k < 4, u0 * xE r * u0 * Yv (c + k) = Yv (c + k) * (u0 * xE r * u0) := by
  rcases bIf_cases H with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inl ⟨_, land_lt, ne_of_ncw (pm_oEl r) (pm_yEl _) h1⟩
  · refine Or.inr fun k hk => ?_
    have hm : u0 * xE r * u0 ∈ H4 := H4.mul_mem (H4.mul_mem u0_mem (cE_mem _ _)) u0_mem
    have e := comm_of_cmB ((pm_comp (pm_lp (e := 2) (by norm_num))
      (pm_comp (pm_oEl r) (pm_lp (e := 2) (by norm_num)))).congr (by simp [LE, u0, mul_assoc]))
      (pm_yEl _) (memP hm) (memP (cE_mem _ _)) (allN_spec h1 k hk)
    exact e

theorem mutS_imp {e f : ℕ} (he : e < 9) (hf : f < 9) (h : mutS e f = true) :
    CFSG.KS.U43Swap.Mut e f := by
  revert h
  unfold CFSG.KS.U43Swap.Mut
  interval_cases e <;> interval_cases f <;> decide

theorem nRec_spec {n : ℕ} (hn : n < 64) (hm : mutS (n / 8 + 1) (n % 8 + 1) = false) :
    ∃ o < 81,
      y9 (n / 8 + 1) * (xE (OD o) * y9 (n % 8 + 1) * (xE (OD o))⁻¹) ≠
        xE (OD o) * y9 (n % 8 + 1) * (xE (OD o))⁻¹ * y9 (n / 8 + 1) ∨
      y9 (n % 8 + 1) * (xE (OD o) * y9 (n / 8 + 1) * (xE (OD o))⁻¹) ≠
        xE (OD o) * y9 (n / 8 + 1) * (xE (OD o))⁻¹ * y9 (n % 8 + 1) := by
  have H0 : CFSG.KC.U43Swap.nRec PT OD NW n = true := allN_spec kN n hn
  unfold CFSG.KC.U43Swap.nRec at H0
  have H1 := strictB_elim H0
  have H := strictB_elim H1
  rcases bIf_cases H with ⟨hc, -⟩ | ⟨-, H2⟩
  · exact absurd (hm.symm.trans hc) Bool.false_ne_true
  have H2' := strictB_elim H2
  have H3 := (bAnd_iff _ _).1 (strictB_elim H2')
  refine ⟨_, blt_lt H3.1, ?_⟩
  rcases bIf_cases H3.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl (ne_of_ncw (pm_sp (n / 8 + 1)) (pm_oConj _ (pm_sp (n % 8 + 1))) h)
  · exact Or.inr (ne_of_ncw (pm_sp (n % 8 + 1)) (pm_oConj _ (pm_sp (n / 8 + 1))) h)

theorem qRec_spec {i : ℕ} (hi : i < 64) : (0 < i → QR (i - 1) >>> 28 < QR i >>> 28) ∧
    keyOK (QR i >>> 28) (cp PT (QR i) 1) = true ∧ keyOK (QR i >>> 58) (cp PT (QR i) 3) = true := by
  have h := (bAnd_iff _ _).1 (strictB_elim (allN_spec kQ i hi))
  refine ⟨fun hi0 => ?_, ((bAnd_iff _ _).1 h.2).1, ((bAnd_iff _ _).1 h.2).2⟩
  rcases bIf_cases h.1 with ⟨hc, -⟩ | ⟨-, hc⟩
  · exact absurd (Nat.eq_of_beq_eq_true hc) (Nat.pos_iff_ne_zero.1 hi0)
  · exact blt_lt hc

theorem kRec_spec {i : ℕ} (hi : i < 128) : (i % 16 ≠ 0 → KC (i - 1) >>> 28 < KC i >>> 28) ∧
    keyOK (KC i >>> 28) (cp PT (KC i) (i / 16 + 1)) = true := by
  have h := (bAnd_iff _ _).1 (strictB_elim (allN_spec kK i hi))
  refine ⟨fun hm => ?_, h.2⟩
  rcases bIf_cases h.1 with ⟨hc, -⟩ | ⟨-, hc⟩
  · exact absurd (Nat.eq_of_beq_eq_true hc) hm
  · exact blt_lt hc

theorem keys_agree {k k' : ℕ} {f g : ℕ → ℕ} {x : G820} (hf : PM f x) (hg : PM g x)
    (h : keyOK k f = true) (h' : keyOK k' g = true) : k % 2 ^ 30 = k' % 2 ^ 30 := by
  have p0 : (0 : ℕ) < 820 := by norm_num
  have p1 : (1 : ℕ) < 820 := by norm_num
  have p9 : (9 : ℕ) < 820 := by norm_num
  rw [keyOK_iff, hf 0 p0, hf 1 p1, hf 9 p9] at h
  rw [keyOK_iff, hg 0 p0, hg 1 p1, hg 9 p9] at h'
  omega

theorem shr_hi {A : ℕ} (h : A >>> 88 = 0) : A >>> 28 = (A >>> 28) % 2 ^ 30 +
    2 ^ 30 * ((A >>> 58) % 2 ^ 30) := by
  rw [Nat.shiftRight_eq_div_pow] at h ⊢
  rw [Nat.shiftRight_eq_div_pow]
  have h' : A < 2 ^ 88 := by
    rcases Nat.lt_or_ge A (2 ^ 88) with hA | hA
    · exact hA
    · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.div_pos hA (by positivity)))
  norm_num at h' ⊢
  omega

theorem shr_hi' {A : ℕ} (h : A >>> 58 = 0) : A >>> 28 = (A >>> 28) % 2 ^ 30 := by
  rw [Nat.shiftRight_eq_div_pow] at h ⊢
  have h' : A < 2 ^ 58 := by
    rcases Nat.lt_or_ge A (2 ^ 58) with hA | hA
    · exact hA
    · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.div_pos hA (by positivity)))
  norm_num at h' ⊢
  omega

theorem kHi_spec : allN 64 (fun i => Nat.beq (Nat.shiftRight (QR i) 88) 0) = true ∧
    allN 128 (fun i => Nat.beq (Nat.shiftRight (KC i) 58) 0) = true := by
  have h := kHi
  unfold hiOK at h
  exact (bAnd_iff _ _).1 h

theorem QR_hi {i : ℕ} (hi : i < 64) : QR i >>> 88 = 0 :=
  Nat.eq_of_beq_eq_true (allN_spec kHi_spec.1 i hi)

theorem KC_hi {i : ℕ} (hi : i < 128) : KC i >>> 58 = 0 :=
  Nat.eq_of_beq_eq_true (allN_spec kHi_spec.2 i hi)

theorem hQ_fact : ∀ i < 64, ∀ j < 64,
    wd (QR i) * s0 * (wd (QR i))⁻¹ = wd (QR j) * s0 * (wd (QR j))⁻¹ →
    wd (QR i) * t0 * (wd (QR i))⁻¹ = wd (QR j) * t0 * (wd (QR j))⁻¹ → i = j := by
  have hinj := inj_of_lt (v := fun i => QR i >>> 28) (n := 64) fun i hi0 hi => (qRec_spec hi).1 hi0
  intro i hi j hj e1 e3
  refine hinj i hi j hj ?_
  obtain ⟨-, a1, a3⟩ := qRec_spec hi
  obtain ⟨-, b1, b3⟩ := qRec_spec hj
  have c1 : cE (QR i) 1 = cE (QR j) 1 := by rw [cE, cE, y9_one]; exact e1
  have c3 : cE (QR i) 3 = cE (QR j) 3 := by rw [cE, cE, y9_three]; exact e3
  have k1 := keys_agree (pm_cp (QR i) 1) ((pm_cp (QR j) 1).congr c1.symm) a1 b1
  have k3 := keys_agree (pm_cp (QR i) 3) ((pm_cp (QR j) 3).congr c3.symm) a3 b3
  change QR i >>> 28 = QR j >>> 28
  rw [shr_hi (QR_hi hi), shr_hi (QR_hi hj), k1, k3]

theorem hK_fact {e : ℕ} (he1 : 1 ≤ e) (he : e < 9) : ∀ i < 16, ∀ j < 16,
    wd (KC (16 * (e - 1) + i)) * y9 e * (wd (KC (16 * (e - 1) + i)))⁻¹ =
      wd (KC (16 * (e - 1) + j)) * y9 e * (wd (KC (16 * (e - 1) + j)))⁻¹ → i = j := by
  have hinj := inj_of_lt (v := fun m => KC (16 * (e - 1) + m) >>> 28) (n := 16)
    fun m hm0 hm => by
      have h := (kRec_spec (i := 16 * (e - 1) + m) (by omega)).1 (by omega)
      have hx : 16 * (e - 1) + m - 1 = 16 * (e - 1) + (m - 1) := by omega
      rw [hx] at h
      exact h
  intro i hi j hj ec
  refine hinj i hi j hj ?_
  have a := (kRec_spec (i := 16 * (e - 1) + i) (by omega)).2
  have b := (kRec_spec (i := 16 * (e - 1) + j) (by omega)).2
  have ha : (16 * (e - 1) + i) / 16 + 1 = e := by omega
  have hb : (16 * (e - 1) + j) / 16 + 1 = e := by omega
  rw [ha] at a
  rw [hb] at b
  have k := keys_agree (pm_cp _ e) ((pm_cp _ e).congr (by rw [cE, cE]; exact ec.symm)) a b
  exact (shr_hi' (KC_hi (i := 16 * (e - 1) + i) (by omega))).trans
    (k.trans (shr_hi' (KC_hi (i := 16 * (e - 1) + j) (by omega))).symm)

theorem CP0_mem_H4 : CP 0 ∈ H4 := by
  rw [← m5_a]
  exact evalG_mem_H4 (by decide)

theorem s0_cube : s0 ^ 3 = 1 := sig_facts.1

theorem t0_cube (h : s0 ^ 3 = 1) : t0 ^ 3 = 1 := by
  rw [t0_eq, conj_pow', h]
  group

theorem st_comm : s0 * t0 = t0 * s0 := sig_facts.2

theorem u0_sq : u0 * u0 = 1 := by
  have hf := pm_comp (pm_lp (e := 2) (by norm_num)) (pm_lp (e := 2) (by norm_num))
  have h := eq_of_eqB hf pm_id (memP (H4.mul_mem (LE_mem (by norm_num)) (LE_mem (by norm_num))))
    P.one_mem kU
  simpa [LE, u0] using h

theorem nine_S0 : 9 ∣ Nat.card (Subgroup.closure ({s0, t0} : Set G820)) := by
  have h3 := s0_cube
  obtain ⟨k1, k2, k3, k4⟩ := kSig_spec
  have hs1 : m5 1 ≠ 1 := ne_of_baseEq (GM_eq 1) id_eq' k1
  have ht1 : evalG m5 sig2W ≠ 1 := ne_of_baseEq (wv_GM _) id_eq' k2
  have ht2 : evalG m5 sig2W ≠ m5 1 := ne_of_baseEq (wv_GM _) (GM_eq 1) k3
  have ht4 : evalG m5 sig2W ≠ m5 1 * m5 1 := by
    have h := ne_of_baseEq (wv_GM _) (wv_GM _) k4
    simpa [evalG, letterVal] using h
  exact CFSG.KS.U43Mod.nine_dvd_card (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) h3 hs1 (t0_cube h3) st_comm ht1 ht2 ht4

theorem xE_pow9 (r : ℕ) : xE r ^ 9 = 1 := by
  rw [xE, cE, conj_pow, y9, CFSG.KS.U43Swap.yE_pow9 s0_cube (t0_cube s0_cube) st_comm]
  group

@[expose] noncomputable def swFacts : CFSG.KS.U43Swap.SwFacts G820 where
  H := H4
  g := m4
  a := CP 0
  s := s0
  t := t0
  u := u0
  X i := xE (OD i)
  Y := Yv
  hH := card_H4
  hHg := rfl
  ha := CP0_mem_H4
  haz h hh := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (H4_le hh)).2
  ha1 := CP0_ne
  ha2 := CP0_sq
  hs := s0_mem
  ht := t0_mem
  hu := u0_mem
  hs3 := s0_cube
  ht3 := t0_cube s0_cube
  hst := st_comm
  hu2 := u0_sq
  hS9 := nine_S0
  hXH _ _ := cE_mem _ _
  hX9 i _ := xE_pow9 _
  hZ e he := by
    have h := (bAnd_iff _ _).1 (strictB_elim (allN_spec kZ e he))
    exact ⟨_, blt_lt h.1, key_X (blt_lt h.1) (pm_sp e) (y9_mem e) h.2⟩
  hCl i hi j hj := by
    have h := (bAnd_iff _ _).1
      (strictB_elim (allN_spec (strictB_elim (allN_spec kOCl i hi)) j hj))
    have hc := blt_lt h.1
    refine ⟨_, hc, key_X hc ((pm_comp (pm_lp (e := j) (by omega)) (pm_comp (pm_oEl (OD i))
      (pm_lp (e := j + 4) (by omega)))).congr ?_) (conj_mem (m4_mem_H4 hj) (cE_mem _ _)) h.2⟩
    simp only [LE, if_pos hj, if_neg (by omega : ¬ j + 4 < 4), Nat.add_sub_cancel, m4_eq hj,
      mul_assoc]
  hYs i hi := by
    have h := (bAnd_iff _ _).1 (strictB_elim (allN_spec kOYm i hi))
    have e := key_Y (k := Nat.land (Nat.shiftRight (OD i) 90) 3)
      (lt_of_lt_of_le land_lt (by norm_num)) (pm_oConj _ (pm_sp 1))
      (conj_mem (cE_mem _ _) (y9_mem 1)) h.1
    rw [y9_one] at e
    exact ⟨_, land_lt, e⟩
  hYt i hi := by
    have h := (bAnd_iff _ _).1 (strictB_elim (allN_spec kOYm i hi))
    have hb := @land_lt (Nat.shiftRight (OD i) 92) 3
    have e := key_Y (k := 4 + Nat.land (Nat.shiftRight (OD i) 92) 3) (by omega)
      (pm_oConj _ (pm_sp 3)) (conj_mem (cE_mem _ _) (y9_mem 3)) h.2
    rw [y9_three] at e
    exact ⟨_, land_lt, e⟩
  hYr k hk := by
    obtain ⟨-, o, ho, h⟩ := yRec_spec hk
    refine ⟨o, ho, (key_Y hk (pm_oConj _ (pm_sp _)) (conj_mem (cE_mem _ _) (y9_mem _)) h).symm.trans
      ?_⟩
    rw [yEk]
    split_ifs
    · rw [y9_one]
    · rw [y9_three]
  hT2a i hi := by
    rcases t2d_spec (h := 4) (c := 0)
      ((bAnd_iff _ _).1 (strictB_elim (allN_spec kOT2 i hi))).1 with h | h
    · exact Or.inl h
    · exact Or.inr fun k hk => by simpa using h k hk
  hT2b i hi := by
    rcases t2d_spec (h := 0) (c := 4)
      ((bAnd_iff _ _).1 (strictB_elim (allN_spec kOT2 i hi))).2 with ⟨k, hk, h⟩ | h
    · exact Or.inl ⟨k, hk, by simpa using h⟩
    · exact Or.inr h
  hTw e he1 he := by
    have H0 : CFSG.KC.U43Swap.tRec PT YR TW (e - 1) = true := allN_spec kT (e - 1) (by omega)
    unfold CFSG.KC.U43Swap.tRec at H0
    have H1 := strictB_elim H0
    have hne := ne_of_ncw (pm_sp (Nat.succ (e - 1))) (pm_yEl _) H1
    have hs : Nat.succ (e - 1) = e := by omega
    rw [hs] at hne
    exact ⟨_, land_lt, hne⟩
  hN e f he1 he hf1 hf hM := by
    have hn : 8 * (e - 1) + (f - 1) < 64 := by omega
    have h1 : (8 * (e - 1) + (f - 1)) / 8 + 1 = e := by omega
    have h2 : (8 * (e - 1) + (f - 1)) % 8 + 1 = f := by omega
    have hm : mutS ((8 * (e - 1) + (f - 1)) / 8 + 1) ((8 * (e - 1) + (f - 1)) % 8 + 1) = false := by
      rw [h1, h2]
      exact Bool.eq_false_iff.2 fun h => hM (mutS_imp he hf h)
    have H := nRec_spec hn hm
    rw [h1, h2] at H
    exact H
  hQ := ⟨fun i => wd (QR i), fun _ _ => wval_mem _ _, hQ_fact⟩
  hK e he1 he := ⟨fun i => wd (KC (16 * (e - 1) + i)), fun _ _ => wval_mem _ _,
    hK_fact he1 he⟩

end CertificateChecks.KernelU43Swap

end
