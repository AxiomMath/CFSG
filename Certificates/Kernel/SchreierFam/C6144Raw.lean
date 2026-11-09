module

public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Certificates.Kernel.Spor.PK.Enc

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.C6144

open CFSG.KS.PK CFSG.Sporadic.Schreier

@[expose] noncomputable def rd (x i : Nat) : Nat := Nat.mod (Nat.div x (Nat.pow 2 (Nat.mul 6 i))) 64

@[expose] noncomputable def mulR (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.mul (rd a (rd b i)) (Nat.pow 2 (Nat.mul 6 i)))) 42

@[expose] def cd (σ : Equiv.Perm (Fin 42)) : Nat :=
  enc 6 (fun i => if h : i < 42 then (σ ⟨i, h⟩ : Nat) else 0) 42

@[expose] def ONE : Nat :=
  4707973897876518275756807182105570957375017328147580252423146288555550842944

theorem rd_eq (x i : Nat) : rd x i = fd 6 x i := rfl

theorem mulR_aux (a b : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.mul (rd a (rd b i)) (Nat.pow 2 (Nat.mul 6 i)))) n =
    enc 6 (fun i => fd 6 a (fd 6 b i)) n
  | 0 => rfl
  | n + 1 => by
    rw [enc_succ, ← mulR_aux a b n]
    rfl

theorem mulR_eq (a b : Nat) : mulR a b = enc 6 (fun i => fd 6 a (fd 6 b i)) 42 := mulR_aux a b 42

theorem cd_bound (σ : Equiv.Perm (Fin 42)) :
    ∀ j < 42, (if h : j < 42 then (σ ⟨j, h⟩ : Nat) else 0) < 2 ^ 6 := by
  intro j hj
  rw [dif_pos hj]
  exact lt_trans (σ _).2 (by norm_num)

theorem fd_cd (σ : Equiv.Perm (Fin 42)) {i : Nat} (hi : i < 42) : fd 6 (cd σ) i = σ ⟨i, hi⟩ := by
  rw [cd, fd_enc (cd_bound σ) hi, dif_pos hi]

theorem cd_inj {σ τ : Equiv.Perm (Fin 42)} (h : cd σ = cd τ) : σ = τ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h1 := fd_cd σ i.2
  have h2 := fd_cd τ i.2
  rw [h] at h1
  exact h1.symm.trans h2

theorem decide_cd (σ τ : Equiv.Perm (Fin 42)) : decide (σ = τ) = Nat.beq (cd σ) (cd τ) := by
  cases hb : Nat.beq (cd σ) (cd τ)
  · refine decide_eq_false fun e => ?_
    rw [e, Nat.beq_refl] at hb
    exact Bool.noConfusion hb
  · exact decide_eq_true (cd_inj (Nat.eq_of_beq_eq_true hb))

theorem cd_mul (σ τ : Equiv.Perm (Fin 42)) : cd (σ * τ) = mulR (cd σ) (cd τ) := by
  rw [mulR_eq, cd]
  apply enc_congr
  intro i hi
  rw [dif_pos hi, fd_cd τ hi, fd_cd σ (τ _).2]
  rfl

set_option maxRecDepth 400000 in
theorem cd_one : cd 1 = ONE := by decide +kernel

@[expose] noncomputable def prodR (Ts : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [ONE] (fun T _ P => T.flatMap fun t => P.map (mulR t)) Ts

theorem prodR_nil : prodR [] = [ONE] := rfl

theorem prodR_cons (T : List Nat) (Ts : List (List Nat)) :
    prodR (T :: Ts) = T.flatMap fun t => (prodR Ts).map (mulR t) := rfl

theorem products_nil42 : products ([] : List (List (Equiv.Perm (Fin 42)))) = [Equiv.refl (Fin 42)] :=
  rfl

set_option maxRecDepth 400000 in
theorem cd_refl : cd (Equiv.refl (Fin 42)) = ONE := by decide +kernel

theorem prodR_eq_nil : (products ([] : List (List (Equiv.Perm (Fin 42))))).map cd = prodR [] := by
  rw [products_nil42, List.map_cons, List.map_nil, cd_refl, prodR_nil]

theorem map_cd_mul (t : Equiv.Perm (Fin 42)) (L : List (Equiv.Perm (Fin 42))) :
    (L.map (t * ·)).map cd = (L.map cd).map (mulR (cd t)) := by
  induction L with
  | nil => rw [List.map_nil, List.map_nil, List.map_nil]
  | cons x L ih => rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, cd_mul, ih]

theorem prodR_eq_cons (T : List (Equiv.Perm (Fin 42))) (Ps : List (List (Equiv.Perm (Fin 42))))
    (ih : (products Ps).map cd = prodR (Ps.map (List.map cd))) :
    (products (T :: Ps)).map cd = prodR ((T :: Ps).map (List.map cd)) := by
  rw [products, List.map_cons, prodR_cons, ← ih, List.map_flatMap, List.flatMap_map]
  congr 1
  funext t
  exact map_cd_mul t _

theorem prodR_eq (Ps : List (List (Equiv.Perm (Fin 42)))) :
    (products Ps).map cd = prodR (Ps.map (List.map cd)) := by
  induction Ps with
  | nil => exact prodR_eq_nil
  | cons T Ps ih => exact prodR_eq_cons T Ps ih

theorem filter_length_cd (L : List (Equiv.Perm (Fin 42))) (p : Equiv.Perm (Fin 42) → Bool)
    (q : Nat → Bool) (h : ∀ g, p g = q (cd g)) :
    (L.filter p).length = ((L.map cd).filter q).length := by
  rw [List.filter_map, List.length_map]
  congr 2
  funext g
  exact h g

theorem all_cd (L : List (Equiv.Perm (Fin 42))) (p : Equiv.Perm (Fin 42) → Bool)
    (q : Nat → Bool) (h : ∀ g, p g = q (cd g)) : L.all p = (L.map cd).all q := by
  rw [List.all_map]
  congr 1
  funext g
  exact h g

@[expose] noncomputable def sq4R (s : Nat) : Bool := Bool.and (Nat.beq (mulR s s) ONE) (!Nat.beq s ONE)

@[expose] noncomputable def ord4R (c : Nat) : Bool := sq4R (mulR c c)

@[expose] noncomputable def commR (B c : Nat) : Bool := Nat.beq (mulR c B) (mulR B c)

@[expose] noncomputable def cosR (R B c : Nat) : Bool :=
  !Nat.beq (mulR (mulR R c) B) (mulR B (mulR R c))

theorem orderIs_four {G : Type*} [Group G] [DecidableEq G] (g : G) :
    orderIs g 4 = (decide (g ^ 2 * g ^ 2 = 1) && !decide (g ^ 2 = 1)) := by
  have e4 : g ^ 2 * g ^ 2 = g ^ 4 := by rw [← pow_add]
  rw [e4, Bool.eq_iff_iff, orderIs, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_iff, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨h4, h⟩
    refine ⟨h4, fun h2 => ?_⟩
    have := h 2 (by simp)
    rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0 h2
  · rintro ⟨h4, h2⟩
    refine ⟨h4, fun k hk => ?_⟩
    rw [List.mem_range] at hk
    rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    match k, hk with
    | 0, _ => exact Or.inl rfl
    | 1, _ =>
      refine Or.inr fun h1 => h2 ?_
      rw [pow_one] at h1
      rw [h1, one_pow]
    | 2, _ => exact Or.inr h2
    | 3, _ =>
      refine Or.inr fun h3 => h2 ?_
      have e : g ^ 4 = g ^ 3 * g := pow_succ g 3
      rw [h3, one_mul, h4] at e
      rw [← e, one_pow]

theorem orderIs_cd (g : Equiv.Perm (Fin 42)) : orderIs g 4 = ord4R (cd g) := by
  rw [orderIs_four, decide_cd, decide_cd, cd_mul, pow_two, cd_mul, cd_one]
  rfl

theorem comm_cd (g h : Equiv.Perm (Fin 42)) : decide (g * h = h * g) = commR (cd h) (cd g) := by
  rw [decide_cd, cd_mul, cd_mul]
  rfl

theorem cos_cd (r p h : Equiv.Perm (Fin 42)) :
    decide (r * p * h ≠ h * (r * p)) = cosR (cd r) (cd h) (cd p) := by
  rw [decide_not, decide_cd]
  simp only [cd_mul]
  rfl

theorem rd_cd_fin (σ : Equiv.Perm (Fin 42)) (x : Fin 42) : rd (cd σ) x = σ x := by
  rw [rd_eq, fd_cd σ x.2]

theorem rd_cd_zero (σ : Equiv.Perm (Fin 42)) : rd (cd σ) 0 = σ 0 := rd_cd_fin σ 0

@[expose] noncomputable def fix4R (c j : Nat) : Bool := Nat.beq (rd c (rd c (rd c (rd c j)))) j

@[expose] def brecF (a b : Bool) : Bool := Bool.rec false a b

@[expose] def brecT (a b : Bool) : Bool := Bool.rec a true b

theorem brecF_eq (a b : Bool) : brecF a b = (b && a) := by cases b <;> rfl

theorem brecT_eq (a b : Bool) : brecT a b = (b || a) := by cases b <;> rfl

theorem eq_and_of_imp (a b : Bool) (h : a = true → b = true) : a = (b && a) := by
  cases a <;> cases b <;> simp_all

theorem eq_or_of_imp (a b : Bool) (h : b = true → a = true) : a = (b || a) := by
  cases a <;> cases b <;> simp_all

@[expose] noncomputable def ord4Q (c : Nat) : Bool :=
  brecF (brecF (ord4R c) (fix4R c 21)) (fix4R c 0)

@[expose] noncomputable def commPre (B c : Nat) : Bool := Nat.beq (rd c (rd B 0)) (rd B (rd c 0))

@[expose] noncomputable def commQ (B c : Nat) : Bool := brecF (commR B c) (commPre B c)

@[expose] noncomputable def cosPre (R B c : Nat) : Bool :=
  !Nat.beq (rd R (rd c (rd B 0))) (rd B (rd R (rd c 0)))

@[expose] noncomputable def cosQ (R B c : Nat) : Bool := brecT (cosR R B c) (cosPre R B c)

theorem pow4_apply (g : Equiv.Perm (Fin 42)) (h : g ^ 2 * g ^ 2 = 1) (x : Fin 42) :
    g (g (g (g x))) = x := by
  have e := congrArg (fun σ : Equiv.Perm (Fin 42) => σ x) h
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e
  exact e

theorem fix4_cd (g : Equiv.Perm (Fin 42)) (x : Fin 42) (h : g ^ 2 * g ^ 2 = 1) :
    fix4R (cd g) x = true := by
  simp only [fix4R, rd_cd_fin, pow4_apply g h x, Nat.beq_refl]

theorem orderIs_cdQ (g : Equiv.Perm (Fin 42)) : orderIs g 4 = ord4Q (cd g) := by
  rw [ord4Q, brecF_eq, brecF_eq, ← orderIs_cd, ← Bool.and_assoc]
  refine eq_and_of_imp _ _ fun h => ?_
  have hg : g ^ 2 * g ^ 2 = 1 := by
    rw [orderIs_four, Bool.and_eq_true, decide_eq_true_iff] at h
    exact h.1
  have h0 : fix4R (cd g) 0 = true := fix4_cd g 0 hg
  have h21 : fix4R (cd g) 21 = true := fix4_cd g 21 hg
  rw [h0, h21, Bool.and_self]

theorem comm_cdQ (g h : Equiv.Perm (Fin 42)) : decide (g * h = h * g) = commQ (cd h) (cd g) := by
  rw [commQ, brecF_eq, ← comm_cd]
  refine eq_and_of_imp _ _ fun hc => ?_
  have e : g * h = h * g := by rwa [decide_eq_true_iff] at hc
  have e0 := congrArg (fun σ : Equiv.Perm (Fin 42) => σ 0) e
  simp only [Equiv.Perm.mul_apply] at e0
  simp only [commPre, rd_cd_zero, rd_cd_fin, e0, Nat.beq_refl]

theorem cos_cdQ (r p h : Equiv.Perm (Fin 42)) :
    decide (r * p * h ≠ h * (r * p)) = cosQ (cd r) (cd h) (cd p) := by
  rw [cosQ, brecT_eq, ← cos_cd]
  refine eq_or_of_imp _ _ fun hp => ?_
  rcases Bool.eq_false_or_eq_true (decide (r * p * h ≠ h * (r * p))) with hc | hc
  · exact hc
  · have e : r * p * h = h * (r * p) := by rwa [decide_eq_false_iff_not, not_not] at hc
    have e0 := congrArg (fun σ : Equiv.Perm (Fin 42) => σ 0) e
    simp only [Equiv.Perm.mul_apply] at e0
    have hq : cosPre (cd r) (cd h) (cd p) = false := by
      simp only [cosPre, rd_cd_zero, rd_cd_fin, e0, Nat.beq_refl, Bool.not_true]
    rw [hq] at hp
    exact absurd hp Bool.false_ne_true

end CertificateChecks.KernelSchreierFam.C6144

end
