module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec

public section

namespace CFSG.OddStandard.SmallF3.FritzII.FzNorm

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII

theorem f_add_self : ∀ a : F4c, a + a = 0 := by decide +kernel

theorem f_cases : ∀ a : F4c, a = 0 ∨ a = 1 ∨ a = fzW ∨ a = 1 + fzW := by decide +kernel

@[expose] def lin (p q a : F4c) : F4c :=
  (if a.a = 0 then 0 else p) + (if a.b = 0 then 0 else q)

theorem lin_zero : ∀ p q : F4c, lin p q 0 = 0 := by decide +kernel

theorem lin_one : ∀ p q : F4c, lin p q 1 = p := by decide +kernel

theorem lin_w : ∀ p q : F4c, lin p q fzW = q := by decide +kernel

theorem lin_1w : ∀ p q : F4c, lin p q (1 + fzW) = p + q := by decide +kernel

theorem eq_lin (φ : F4c → F4c) (h : ∀ a a', φ (a + a') = φ a + φ a') :
    ∀ a, φ a = lin (φ 1) (φ fzW) a := by
  have h0 : φ 0 = 0 := by
    have h00 := h 0 0
    rw [add_zero] at h00
    rw [h00]
    exact f_add_self _
  intro a
  rcases f_cases a with rfl | rfl | rfl | rfl
  · rw [h0, lin_zero]
  · rw [lin_one]
  · rw [lin_w]
  · rw [h, lin_1w]

theorem lin_ord3 : ∀ p q : F4c, (∀ c, lin p q (lin p q (lin p q c)) = c) →
    (∀ c, lin p q c = c → c = 0) → (p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1) := by
  decide +kernel

theorem lin_fix : ∀ p q y : F4c, (p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1) →
    ∃ c, y + lin p q c = c := by
  decide +kernel

theorem opt_mul : ∀ x y : F4c, (x = fzW ∨ x = fzW2) → (y = fzW ∨ y = fzW2) → x * y = fzW →
    x = fzW2 ∧ y = fzW2 := by
  decide +kernel

theorem w2_ne_w : fzW2 ≠ fzW := by decide +kernel

theorem f_sq4 : ∀ a : F4c, a * a * (a * a) = a := by decide +kernel

theorem f_frob_add : ∀ a b : F4c, (a + b) * (a + b) = a * a + b * b := by decide +kernel

theorem f_frob3 : ∀ c c' a b : F4c,
    (c + c' + a * b) * (c + c' + a * b) = c * c + c' * c' + a * a * (b * b) := by
  decide +kernel

theorem mul_a (x y : FzUT) : (x * y).a = x.a + y.a := rfl

theorem mul_b (x y : FzUT) : (x * y).b = x.b + y.b := rfl

theorem mul_c (x y : FzUT) : (x * y).c = x.c + y.c + x.a * y.b := rfl

theorem inZ_of_comm (x : FzUT) (h : ∀ y : FzUT, x * y = y * x) : x.a = 0 ∧ x.b = 0 := by
  have h1 := congrArg UT3.c (h ⟨0, 1, 0⟩)
  have h2 := congrArg UT3.c (h ⟨1, 0, 0⟩)
  simp only [mul_c] at h1 h2
  constructor
  · simpa using h1
  · simpa using h2.symm

theorem comm_of_inZ (x : FzUT) (ha : x.a = 0) (hb : x.b = 0) (y : FzUT) : x * y = y * x :=
  UT3.ext (by rw [mul_a, mul_a, add_comm]) (by rw [mul_b, mul_b, add_comm])
    (by rw [mul_c, mul_c, ha, hb, zero_mul, mul_zero, add_comm x.c])

theorem comm_map (σ : MulAut FzUT) (x : FzUT) (h : ∀ y, x * y = y * x) (y : FzUT) :
    σ x * y = y * σ x := by
  obtain ⟨y', rfl⟩ := σ.surjective y
  rw [← map_mul, ← map_mul, h]

theorem comm_of_map (σ : MulAut FzUT) (x : FzUT) (h : ∀ y, σ x * y = y * σ x) (y : FzUT) :
    x * y = y * x :=
  σ.injective (by rw [map_mul, map_mul, h])

theorem inZ_map (σ : MulAut FzUT) (x : FzUT) (ha : x.a = 0) (hb : x.b = 0) :
    (σ x).a = 0 ∧ (σ x).b = 0 :=
  inZ_of_comm _ (comm_map σ x (comm_of_inZ x ha hb))

theorem inZ_of_map (σ : MulAut FzUT) (x : FzUT) (h : (σ x).a = 0 ∧ (σ x).b = 0) :
    x.a = 0 ∧ x.b = 0 :=
  inZ_of_comm _ (comm_of_map σ x (comm_of_inZ _ h.1 h.2))

theorem sq_c (x : FzUT) : (x * x).c = x.a * x.b := by rw [mul_c, f_add_self, zero_add]

theorem ab_of_sq (x : FzUT) (h : x * x = 1) : x.a * x.b = 0 := by
  rw [← sq_c x, h]
  rfl

theorem sq_of_ab (x : FzUT) (h : x.a * x.b = 0) : x * x = 1 :=
  UT3.ext (by rw [mul_a]; exact f_add_self _) (by rw [mul_b]; exact f_add_self _)
    (by rw [sq_c, h]; rfl)

def N1 (x : FzUT) : Prop := x.b = 0 ∧ x.a ≠ 0

def N2 (x : FzUT) : Prop := x.a = 0 ∧ x.b ≠ 0

theorem ncomm (x y : FzUT) (hx : N1 x) (hy : N2 y) : x * y ≠ y * x := by
  intro h
  have hc : x.c + y.c + x.a * y.b = y.c + x.c + y.a * x.b := congrArg UT3.c h
  rw [hy.1, zero_mul, add_zero, add_comm y.c x.c] at hc
  exact mul_ne_zero hx.2 hy.2 (add_left_cancel (hc.trans (add_zero _).symm))

theorem comm1 (u v : FzUT) (hu : u.b = 0) (hv : v.b = 0) : u * v = v * u :=
  UT3.ext (by rw [mul_a, mul_a, add_comm]) (by rw [mul_b, mul_b, add_comm])
    (by rw [mul_c, mul_c, hu, hv, mul_zero, mul_zero, add_comm u.c])

theorem comm2 (u v : FzUT) (hu : u.a = 0) (hv : v.a = 0) : u * v = v * u :=
  UT3.ext (by rw [mul_a, mul_a, add_comm]) (by rw [mul_b, mul_b, add_comm])
    (by rw [mul_c, mul_c, hu, hv, zero_mul, zero_mul, add_comm u.c])

theorem type_map (σ : MulAut FzUT) (x : FzUT) (hx : N1 x ∨ N2 x) : N1 (σ x) ∨ N2 (σ x) := by
  have hsq : x * x = 1 := sq_of_ab x (by
    rcases hx with h | h
    · rw [h.1, mul_zero]
    · rw [h.1, zero_mul])
  have hnz : ¬ (x.a = 0 ∧ x.b = 0) := by
    rintro ⟨ha, hb⟩
    rcases hx with h | h
    · exact h.2 ha
    · exact h.2 hb
  have hsq' : σ x * σ x = 1 := by rw [← map_mul, hsq, map_one]
  have hnz' : ¬ ((σ x).a = 0 ∧ (σ x).b = 0) := fun h => hnz (inZ_of_map σ x h)
  rcases mul_eq_zero.mp (ab_of_sq _ hsq') with h | h
  · exact Or.inr ⟨h, fun hb => hnz' ⟨h, hb⟩⟩
  · exact Or.inl ⟨h, fun ha => hnz' ⟨ha, h⟩⟩

theorem swap1 (σ : MulAut FzUT) {x : FzUT} (hx : N1 x) (hσx : N2 (σ x)) {y : FzUT}
    (hy : N2 y) : N1 (σ y) := by
  rcases type_map σ y (Or.inr hy) with h | h
  · exact h
  · exact absurd (σ.injective (by rw [map_mul, map_mul]; exact comm2 _ _ hσx.1 h.1))
      (ncomm x y hx hy)

theorem swap2 (σ : MulAut FzUT) {x : FzUT} (hx : N2 x) (hσx : N1 (σ x)) {y : FzUT}
    (hy : N1 y) : N2 (σ y) := by
  rcases type_map σ y (Or.inl hy) with h | h
  · exact absurd (σ.injective (by rw [map_mul, map_mul]; exact comm1 _ _ h.1 hσx.1))
      (ncomm y x hy hx)
  · exact h

theorem keep1 (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) {x : FzUT} (hx : N1 x) :
    N1 (σ x) := by
  rcases type_map σ x (Or.inl hx) with h | h
  · exact h
  · have h2 : N1 (σ (σ x)) := swap1 σ hx h h
    have h3' : N2 (σ (σ (σ x))) := swap2 σ h h2 h2
    rw [h3] at h3'
    exact absurd h3'.1 hx.2

theorem keep2 (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) {x : FzUT} (hx : N2 x) :
    N2 (σ x) := by
  rcases type_map σ x (Or.inr hx) with h | h
  · have h2 : N2 (σ (σ x)) := swap2 σ hx h h
    have h3' : N1 (σ (σ (σ x))) := swap1 σ h h2 h2
    rw [h3] at h3'
    exact absurd h3'.1 hx.2
  · exact h

theorem b_map (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (x : FzUT) (hb : x.b = 0) :
    (σ x).b = 0 := by
  by_cases ha : x.a = 0
  · exact (inZ_map σ x ha hb).2
  · exact (keep1 σ h3 ⟨hb, ha⟩).1

theorem a_map (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (x : FzUT) (ha : x.a = 0) :
    (σ x).a = 0 := by
  by_cases hb : x.b = 0
  · exact (inZ_map σ x ha hb).1
  · exact (keep2 σ h3 ⟨ha, hb⟩).1

def aS (σ : MulAut FzUT) (a : F4c) : F4c := (σ ⟨a, 0, 0⟩).a

def fS (σ : MulAut FzUT) (a : F4c) : F4c := (σ ⟨a, 0, 0⟩).c

def bS (σ : MulAut FzUT) (b : F4c) : F4c := (σ ⟨0, b, 0⟩).b

def gS (σ : MulAut FzUT) (b : F4c) : F4c := (σ ⟨0, b, 0⟩).c

def zS (σ : MulAut FzUT) (c : F4c) : F4c := (σ ⟨0, 0, c⟩).c

theorem sZ (σ : MulAut FzUT) (c : F4c) : σ ⟨0, 0, c⟩ = ⟨0, 0, zS σ c⟩ := by
  have h := inZ_map σ ⟨0, 0, c⟩ rfl rfl
  exact UT3.ext h.1 h.2 rfl

theorem sA (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (a c : F4c) :
    σ ⟨a, 0, c⟩ = ⟨aS σ a, 0, fS σ a + zS σ c⟩ := by
  have e : (⟨a, 0, c⟩ : FzUT) = ⟨a, 0, 0⟩ * ⟨0, 0, c⟩ := by
    ext <;> simp [mul_a, mul_b, mul_c]
  have hu := b_map σ h3 ⟨a, 0, 0⟩ rfl
  have hv := inZ_map σ ⟨0, 0, c⟩ rfl rfl
  rw [e, map_mul]
  refine UT3.ext ?_ ?_ ?_
  · rw [mul_a, hv.1, add_zero]; rfl
  · rw [mul_b, hu, hv.2, add_zero]
  · rw [mul_c, hv.2, mul_zero, add_zero]; rfl

theorem sB (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (b c : F4c) :
    σ ⟨0, b, c⟩ = ⟨0, bS σ b, gS σ b + zS σ c⟩ := by
  have e : (⟨0, b, c⟩ : FzUT) = ⟨0, b, 0⟩ * ⟨0, 0, c⟩ := by
    ext <;> simp [mul_a, mul_b, mul_c]
  have hu := a_map σ h3 ⟨0, b, 0⟩ rfl
  have hv := inZ_map σ ⟨0, 0, c⟩ rfl rfl
  rw [e, map_mul]
  refine UT3.ext ?_ ?_ ?_
  · rw [mul_a, hu, hv.1, add_zero]
  · rw [mul_b, hv.2, add_zero]; rfl
  · rw [mul_c, hv.2, mul_zero, add_zero]; rfl

theorem sA0 (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (a : F4c) :
    σ ⟨a, 0, 0⟩ = ⟨aS σ a, 0, fS σ a⟩ :=
  UT3.ext rfl (b_map σ h3 ⟨a, 0, 0⟩ rfl) rfl

theorem sB0 (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (b : F4c) :
    σ ⟨0, b, 0⟩ = ⟨0, bS σ b, gS σ b⟩ :=
  UT3.ext (a_map σ h3 ⟨0, b, 0⟩ rfl) rfl rfl

theorem zS_add (σ : MulAut FzUT) (c c' : F4c) : zS σ (c + c') = zS σ c + zS σ c' := by
  have e : (⟨0, 0, c + c'⟩ : FzUT) = ⟨0, 0, c⟩ * ⟨0, 0, c'⟩ := by
    ext <;> simp [mul_a, mul_b, mul_c]
  change (σ ⟨0, 0, c + c'⟩).c = (σ ⟨0, 0, c⟩).c + (σ ⟨0, 0, c'⟩).c
  rw [e, map_mul, mul_c, (inZ_map σ ⟨0, 0, c⟩ rfl rfl).1, zero_mul, add_zero]

theorem sA_mul (σ : MulAut FzUT) (a a' : F4c) :
    σ ⟨a + a', 0, 0⟩ = σ ⟨a, 0, 0⟩ * σ ⟨a', 0, 0⟩ := by
  rw [← map_mul]
  exact congrArg σ (by ext <;> simp [mul_a, mul_b, mul_c])

theorem sB_mul (σ : MulAut FzUT) (b b' : F4c) :
    σ ⟨0, b + b', 0⟩ = σ ⟨0, b, 0⟩ * σ ⟨0, b', 0⟩ := by
  rw [← map_mul]
  exact congrArg σ (by ext <;> simp [mul_a, mul_b, mul_c])

theorem aS_add (σ : MulAut FzUT) (a a' : F4c) : aS σ (a + a') = aS σ a + aS σ a' := by
  change (σ ⟨a + a', 0, 0⟩).a = (σ ⟨a, 0, 0⟩).a + (σ ⟨a', 0, 0⟩).a
  rw [sA_mul, mul_a]

theorem fS_add (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (a a' : F4c) :
    fS σ (a + a') = fS σ a + fS σ a' := by
  change (σ ⟨a + a', 0, 0⟩).c = (σ ⟨a, 0, 0⟩).c + (σ ⟨a', 0, 0⟩).c
  rw [sA_mul, mul_c, b_map σ h3 ⟨a', 0, 0⟩ rfl, mul_zero, add_zero]

theorem bS_add (σ : MulAut FzUT) (b b' : F4c) : bS σ (b + b') = bS σ b + bS σ b' := by
  change (σ ⟨0, b + b', 0⟩).b = (σ ⟨0, b, 0⟩).b + (σ ⟨0, b', 0⟩).b
  rw [sB_mul, mul_b]

theorem gS_add (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (b b' : F4c) :
    gS σ (b + b') = gS σ b + gS σ b' := by
  change (σ ⟨0, b + b', 0⟩).c = (σ ⟨0, b, 0⟩).c + (σ ⟨0, b', 0⟩).c
  rw [sB_mul, mul_c, a_map σ h3 ⟨0, b, 0⟩ rfl, zero_mul, add_zero]

theorem zeta_opt (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x)
    (hf : ∀ x, x ≠ 1 → σ x ≠ x) : ∃ p q : F4c, ((p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1)) ∧
      ∀ c, zS σ c = lin p q c := by
  obtain ⟨p, q, hl⟩ : ∃ p q, ∀ c, zS σ c = lin p q c := ⟨_, _, eq_lin _ (zS_add σ)⟩
  refine ⟨p, q, lin_ord3 p q (fun c => ?_) (fun c hc => ?_), hl⟩
  · have h := congrArg UT3.c (h3 ⟨0, 0, c⟩)
    rw [sZ, sZ, sZ] at h
    simpa only [hl] using h
  · rw [← hl] at hc
    by_contra hc0
    apply hf ⟨0, 0, c⟩ (fun h => hc0 (congrArg UT3.c h))
    rw [sZ, hc]

theorem alpha_opt (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x)
    (hf : ∀ x, x ≠ 1 → σ x ≠ x) : ∃ p q : F4c, ((p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1)) ∧
      ∀ a, aS σ a = lin p q a := by
  obtain ⟨pz, qz, hoz, hz⟩ := zeta_opt σ h3 hf
  obtain ⟨p, q, hl⟩ : ∃ p q, ∀ a, aS σ a = lin p q a := ⟨_, _, eq_lin _ (aS_add σ)⟩
  refine ⟨p, q, lin_ord3 p q (fun a => ?_) (fun a ha => ?_), hl⟩
  · have h := congrArg UT3.a (h3 ⟨a, 0, 0⟩)
    rw [sA σ h3, sA σ h3, sA σ h3] at h
    simpa only [hl] using h
  · rw [← hl] at ha
    by_contra ha0
    obtain ⟨c, hc⟩ := lin_fix pz qz (fS σ a) hoz
    rw [← hz] at hc
    apply hf ⟨a, 0, c⟩ (fun h => ha0 (congrArg UT3.a h))
    rw [sA σ h3, ha, hc]

theorem beta_opt (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x)
    (hf : ∀ x, x ≠ 1 → σ x ≠ x) : ∃ p q : F4c, ((p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1)) ∧
      ∀ b, bS σ b = lin p q b := by
  obtain ⟨pz, qz, hoz, hz⟩ := zeta_opt σ h3 hf
  obtain ⟨p, q, hl⟩ : ∃ p q, ∀ b, bS σ b = lin p q b := ⟨_, _, eq_lin _ (bS_add σ)⟩
  refine ⟨p, q, lin_ord3 p q (fun b => ?_) (fun b hb => ?_), hl⟩
  · have h := congrArg UT3.b (h3 ⟨0, b, 0⟩)
    rw [sB σ h3, sB σ h3, sB σ h3] at h
    simpa only [hl] using h
  · rw [← hl] at hb
    by_contra hb0
    obtain ⟨c, hc⟩ := lin_fix pz qz (gS σ b) hoz
    rw [← hz] at hc
    apply hf ⟨0, b, c⟩ (fun h => hb0 (congrArg UT3.b h))
    rw [sB σ h3, hb, hc]

theorem comm_rel (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) :
    aS σ 1 * bS σ 1 = zS σ 1 := by
  have e : (⟨1, 0, 0⟩ * ⟨0, 1, 0⟩ : FzUT) = ⟨0, 1, 0⟩ * ⟨1, 0, 0⟩ * ⟨0, 0, 1⟩ := by
    decide +kernel
  have h := congrArg UT3.c (congrArg σ e)
  rw [map_mul, map_mul, map_mul, sA0 σ h3, sB0 σ h3, sZ] at h
  simp only [mul_a, mul_b, mul_c, mul_zero, zero_mul, add_zero, zero_add] at h
  linear_combination h

@[expose] def iA (x : F4c × F4c) : FzUT := ⟨x.1, 0, x.2⟩

@[expose] def iB (x : F4c × F4c) : FzUT := ⟨0, x.1, x.2⟩

@[expose] def mA (pf qf : F4c) (x : F4c × F4c) : F4c × F4c :=
  (lin fzW2 1 x.1, lin pf qf x.1 + lin fzW fzW2 x.2)

@[expose] def rA (x : F4c × F4c) : F4c × F4c := (fzW2 * x.1, fzW * x.2)

theorem braid_model : ∀ pf qf : F4c,
    (∀ a, mA pf qf (mA pf qf (mA pf qf (a, 0))) = (a, 0)) →
    mA pf qf (rA (mA pf qf (1, 0))) = rA (mA pf qf (rA (1, 0))) ∧
    mA pf qf (rA (mA pf qf (fzW, 0))) = rA (mA pf qf (rA (fzW, 0))) := by
  decide +kernel

theorem rho_iA (x : F4c × F4c) : fzRho0 (iA x) = iA (rA x) :=
  UT3.ext rfl (mul_zero fzW2) rfl

theorem rho_iB (x : F4c × F4c) : fzRho0 (iB x) = iB (rA x) :=
  UT3.ext (mul_zero fzW2) rfl rfl

theorem iA_inj {x y : F4c × F4c} (h : iA x = iA y) : x = y :=
  Prod.ext (congrArg UT3.a h) (congrArg UT3.c h)

theorem iB_inj {x y : F4c × F4c} (h : iB x = iB y) : x = y :=
  Prod.ext (congrArg UT3.b h) (congrArg UT3.c h)

theorem braid_A (σ : MulAut FzUT) (h3 : ∀ x, σ (σ (σ x)) = x) (hf : ∀ x, x ≠ 1 → σ x ≠ x)
    (hz1 : zS σ 1 = fzW) (x : FzUT) : σ (fzRho0 (σ x)) = fzRho0 (σ (fzRho0 x)) := by
  obtain ⟨pz, qz, hoz, hz⟩ := zeta_opt σ h3 hf
  have hpz : pz = fzW := by rw [← lin_one pz qz, ← hz, hz1]
  have hqz : qz = fzW2 := by
    rcases hoz with h | h
    · exact h.2
    · exact absurd (h.1.symm.trans hpz) w2_ne_w
  obtain ⟨pa, qa, hoa, ha⟩ := alpha_opt σ h3 hf
  obtain ⟨pb, qb, hob, hb⟩ := beta_opt σ h3 hf
  have hab : pa * pb = fzW := by
    rw [← lin_one pa qa, ← lin_one pb qb, ← ha, ← hb, comm_rel σ h3, hz1]
  have hw : ∀ p q : F4c, ((p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1)) → p = fzW ∨ p = fzW2 :=
    fun p q h => h.imp And.left And.left
  obtain ⟨hpa, hpb⟩ := opt_mul pa pb (hw _ _ hoa) (hw _ _ hob) hab
  have hq : ∀ p q : F4c, ((p = fzW ∧ q = fzW2) ∨ (p = fzW2 ∧ q = 1)) → p = fzW2 → q = 1 :=
    fun p q h hp => h.elim (fun h' => absurd (hp.symm.trans h'.1) w2_ne_w) And.right
  have hqa := hq _ _ hoa hpa
  have hqb := hq _ _ hob hpb
  subst hpz hqz hpa hqa hpb hqb
  obtain ⟨pf, qf, hfl⟩ : ∃ p q, ∀ a, fS σ a = lin p q a := ⟨_, _, eq_lin _ (fS_add σ h3)⟩
  obtain ⟨pg, qg, hgl⟩ : ∃ p q, ∀ b, gS σ b = lin p q b := ⟨_, _, eq_lin _ (gS_add σ h3)⟩
  have hA : ∀ y, σ (iA y) = iA (mA pf qf y) := by
    intro y
    change σ ⟨y.1, 0, y.2⟩ = _
    rw [sA σ h3, ha, hfl, hz]
    rfl
  have hB : ∀ y, σ (iB y) = iB (mA pg qg y) := by
    intro y
    change σ ⟨0, y.1, y.2⟩ = _
    rw [sB σ h3, hb, hgl, hz]
    rfl
  have cA : ∀ a, mA pf qf (mA pf qf (mA pf qf (a, 0))) = (a, 0) := fun a =>
    iA_inj (by rw [← hA, ← hA, ← hA]; exact h3 _)
  have cB : ∀ b, mA pg qg (mA pg qg (mA pg qg (b, 0))) = (b, 0) := fun b =>
    iB_inj (by rw [← hB, ← hB, ← hB]; exact h3 _)
  have bA := braid_model pf qf cA
  have bB := braid_model pg qg cB
  have key : fzGens (σ * fzRho0 * σ) = fzGens (fzRho0 * σ * fzRho0) := by
    refine FzAutD.ext ?_ ?_ ?_ ?_
    · change σ (fzRho0 (σ (iA (1, 0)))) = fzRho0 (σ (fzRho0 (iA (1, 0))))
      rw [hA, rho_iA, hA, rho_iA, hA, rho_iA, bA.1]
    · change σ (fzRho0 (σ (iA (fzW, 0)))) = fzRho0 (σ (fzRho0 (iA (fzW, 0))))
      rw [hA, rho_iA, hA, rho_iA, hA, rho_iA, bA.2]
    · change σ (fzRho0 (σ (iB (1, 0)))) = fzRho0 (σ (fzRho0 (iB (1, 0))))
      rw [hB, rho_iB, hB, rho_iB, hB, rho_iB, bB.1]
    · change σ (fzRho0 (σ (iB (fzW, 0)))) = fzRho0 (σ (fzRho0 (iB (fzW, 0))))
      rw [hB, rho_iB, hB, rho_iB, hB, rho_iB, bB.2]
  have h := fzEv_gens (σ * fzRho0 * σ) x
  rw [key, fzEv_gens] at h
  exact h.symm

@[expose] def fzFrob : MulAut FzUT where
  toFun x := ⟨x.a * x.a, x.b * x.b, x.c * x.c⟩
  invFun x := ⟨x.a * x.a, x.b * x.b, x.c * x.c⟩
  left_inv x := UT3.ext (f_sq4 _) (f_sq4 _) (f_sq4 _)
  right_inv x := UT3.ext (f_sq4 _) (f_sq4 _) (f_sq4 _)
  map_mul' x y := UT3.ext (f_frob_add _ _) (f_frob_add _ _) (f_frob3 _ _ _ _)

theorem frob_frob (x : FzUT) : fzFrob (fzFrob x) = x :=
  UT3.ext (f_sq4 _) (f_sq4 _) (f_sq4 _)

theorem frob_c (x : FzUT) : (fzFrob x).c = x.c * x.c := rfl

theorem frob_z1 : fzFrob ⟨0, 0, 1⟩ = ⟨0, 0, 1⟩ := by decide +kernel

theorem fzNormSpec : FzNormSpec := by
  intro σ h3 hf
  obtain ⟨p, q, hopt, hz⟩ := zeta_opt σ h3 hf
  rcases hopt with ⟨hp, -⟩ | ⟨hp, -⟩
  · have hz1 : zS σ 1 = fzW := by rw [hz, lin_one, hp]
    refine ⟨fzRho0 * σ * fzRho0, fun x => ?_⟩
    change fzRho0 (σ (fzRho0 (σ x))) = fzRho0 (fzRho0 (σ (fzRho0 x)))
    rw [braid_A σ h3 hf hz1 x]
  · obtain ⟨τ, hτ⟩ : ∃ τ : MulAut FzUT, ∀ x, τ x = fzFrob (σ (fzFrob x)) :=
      ⟨fzFrob * σ * fzFrob, fun _ => rfl⟩
    have h3' : ∀ x, τ (τ (τ x)) = x := by
      intro x
      simp only [hτ, frob_frob, h3]
    have hf' : ∀ x, x ≠ 1 → τ x ≠ x := by
      intro x hx h
      have h' : σ (fzFrob x) = fzFrob x := by
        have := congrArg fzFrob h
        rwa [hτ, frob_frob] at this
      apply hf (fzFrob x) _ h'
      intro h1
      apply hx
      rw [← frob_frob x, h1, map_one]
    have hz1 : zS τ 1 = fzW := by
      change (τ ⟨0, 0, 1⟩).c = fzW
      rw [hτ, frob_z1, frob_c]
      change zS σ 1 * zS σ 1 = fzW
      rw [hz, lin_one, hp]
      decide +kernel
    refine ⟨fzRho0 * τ * fzRho0 * fzFrob, fun x => ?_⟩
    change fzRho0 (τ (fzRho0 (fzFrob (σ x)))) = fzRho0 (fzRho0 (τ (fzRho0 (fzFrob x))))
    have e : fzFrob (σ x) = τ (fzFrob x) := by rw [hτ, frob_frob]
    rw [e, braid_A τ h3' hf' hz1]

end CFSG.OddStandard.SmallF3.FritzII.FzNorm
