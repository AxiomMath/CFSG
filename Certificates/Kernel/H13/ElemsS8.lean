module

public import CFSG.Quasithin.H13.L32NS8Inputs
public import CFSG.Certificates.Kernel.Mat8PSound
public import Certificates.Kernel.H13.Data
public import Certificates.Kernel.H13.DataS8P

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P

inductive S8T where
  | lf : S8T
  | nd : S8T → ℕ → S8T → S8T

@[expose] noncomputable def s8Split (l : List ℕ) : List ℕ × List ℕ :=
  List.rec (motive := fun _ => List ℕ × List ℕ) ([], []) (fun x _ ih => (x :: ih.2, ih.1)) l

@[expose] noncomputable def s8Nd (f : List ℕ → S8T) (x : ℕ) (p : List ℕ × List ℕ) : S8T :=
  S8T.nd (f p.1) x (f p.2)

@[expose] noncomputable def s8OfT (n : ℕ) : List ℕ → S8T :=
  Nat.rec (motive := fun _ => List ℕ → S8T) (fun _ => S8T.lf)
    (fun _ ih l => List.rec (motive := fun _ => S8T) S8T.lf (fun x t _ => s8Nd ih x (s8Split t)) l)
    n

@[expose] noncomputable def s8GetT (T : S8T) : ℕ → ℕ :=
  S8T.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ x _ ihl ihr i => Nat.rec (motive := fun _ => ℕ) x
      (fun j _ => Bool.rec (motive := fun _ => ℕ) (ihr (j / 2)) (ihl (j / 2))
        (Nat.beq (j % 2) 0)) i) T

@[expose] noncomputable def s8Chk (T : S8T) (gp xs : List ℕ) : ℕ → List ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → Bool) (fun _ _ => true)
    (fun x _ ih k cs => List.rec (motive := fun _ => Bool) false
      (fun c cs' _ => Nat.blt (c / 8) k &&
        (Nat.beq x (mulP (gp.getD (c % 8) oneP) (s8GetT T (c / 8))) && ih (k + 1) cs')) cs) xs

@[expose] noncomputable def s8WB (M cs : List ℕ) : Bool :=
  Nat.beq (M.headD 0) oneP &&
    s8Chk (s8OfT M.length M) (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) M.tail 1 cs

theorem s8Split_eq : ∀ (l : List ℕ) (k : ℕ),
    (s8Split l).1.getD k 0 = l.getD (2 * k) 0 ∧ (s8Split l).2.getD k 0 = l.getD (2 * k + 1) 0
  | [], k => by simp [s8Split]
  | x :: l, k => by
    have e : s8Split (x :: l) = (x :: (s8Split l).2, (s8Split l).1) := rfl
    rw [e]
    cases k with
    | zero =>
      refine ⟨by simp, ?_⟩
      rw [(s8Split_eq l 0).1]
      simp
    | succ k =>
      have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      refine ⟨?_, ?_⟩
      · rw [List.getD_cons_succ, (s8Split_eq l k).2, e2, List.getD_cons_succ]
      · rw [List.getD_cons_succ, (s8Split_eq l (k + 1)).1]

theorem s8Split_length : ∀ l : List ℕ,
    (s8Split l).1.length ≤ (l.length + 1) / 2 ∧ (s8Split l).2.length ≤ l.length / 2
  | [] => by simp [s8Split]
  | x :: l => by
    have e : s8Split (x :: l) = (x :: (s8Split l).2, (s8Split l).1) := rfl
    rw [e]
    obtain ⟨h1, h2⟩ := s8Split_length l
    simp only [List.length_cons]
    omega

theorem s8GetT_ofT : ∀ (n : ℕ) (l : List ℕ), l.length ≤ n → ∀ i,
    s8GetT (s8OfT n l) i = l.getD i 0
  | 0, l, h, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]
    rfl
  | n + 1, [], _, i => by simp only [List.getD_nil]; rfl
  | n + 1, x :: l, h, 0 => rfl
  | n + 1, x :: l, h, i + 1 => by
    simp only [List.length_cons] at h
    obtain ⟨hl1, hl2⟩ := s8Split_length l
    have e : s8GetT (s8OfT (n + 1) (x :: l)) (i + 1) =
        Bool.rec (motive := fun _ => ℕ) (s8GetT (s8OfT n (s8Split l).2) (i / 2))
          (s8GetT (s8OfT n (s8Split l).1) (i / 2)) (Nat.beq (i % 2) 0) := rfl
    rw [e, List.getD_cons_succ]
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · have hb : Nat.beq (i % 2) 0 = true := by rw [hi]; rfl
      rw [hb]
      change s8GetT (s8OfT n (s8Split l).1) (i / 2) = _
      rw [s8GetT_ofT n _ (by omega), (s8Split_eq l _).1]
      congr 1
      omega
    · have hb : Nat.beq (i % 2) 0 = false := by rw [hi]; rfl
      rw [hb]
      change s8GetT (s8OfT n (s8Split l).2) (i / 2) = _
      rw [s8GetT_ofT n _ (by omega), (s8Split_eq l _).2]
      congr 1
      omega

theorem s8Chk_sound (T : S8T) (gp : List ℕ) (P : ℕ → Prop) (M : List ℕ)
    (hT : ∀ j < M.length, s8GetT T j = M.getD j 0)
    (hstep : ∀ i y, P y → P (mulP (gp.getD i oneP) y)) :
    ∀ (xs : List ℕ) (k : ℕ) (cs : List ℕ), s8Chk T gp xs k cs = true → M.drop k = xs →
      (∀ j < k, P (M.getD j 0)) → ∀ j < M.length, P (M.getD j 0)
  | [], k, _, _, hd, hk => fun j hj => hk j (by
      have := List.drop_eq_nil_iff.mp hd
      omega)
  | _ :: _, _, [], h, _, _ => absurd h Bool.false_ne_true
  | x :: xs, k, c :: cs, h, hd, hk => by
    have h' : (Nat.blt (c / 8) k && (Nat.beq x (mulP (gp.getD (c % 8) oneP) (s8GetT T (c / 8))) &&
        s8Chk T gp xs (k + 1) cs)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨hlt, hx, hr⟩ := h'
    have hkM : k < M.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hd
      exact List.cons_ne_nil _ _ hd.symm
    rw [List.drop_eq_getElem_cons hkM, List.cons.injEq] at hd
    have hPx : P (M.getD k 0) := by
      rw [List.getD_eq_getElem _ _ hkM, hd.1, hx, hT _ (by omega)]
      exact hstep _ _ (hk _ hlt)
    refine s8Chk_sound T gp P M hT hstep xs (k + 1) cs hr hd.2 fun j hj => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hk j hj
    · exact hPx

set_option maxRecDepth 100000 in
theorem s8WB_true : s8WB D.s8L.reverse D.s8P = true := by decide +kernel

theorem s8_step (i y : ℕ) (h : y < 2 ^ 64 ∧ ∃ w, unpackM y = evalW CFSG.Quasithin.H13.S8Cert.s8G w) :
    let z := mulP ((CFSG.Quasithin.H13.S8Cert.s8G.map code64R).getD i oneP) y
    z < 2 ^ 64 ∧ ∃ w, unpackM z = evalW CFSG.Quasithin.H13.S8Cert.s8G w := by
  obtain ⟨-, w, hw⟩ := h
  refine ⟨mulP_lt _ _, i :: w, ?_⟩
  rw [← mul8_unpackM, hw, ← getD_unpack _ (by decide) i]
  rfl

theorem s8WB_words {M cs : List ℕ} (h : s8WB M cs = true) :
    ∀ y ∈ M, y < 2 ^ 64 ∧ ∃ w, unpackM y = evalW CFSG.Quasithin.H13.S8Cert.s8G w := by
  rw [s8WB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, hc⟩ := h
  have hhd : ∀ l : List ℕ, l.getD 0 0 = l.headD 0 := fun l => by cases l <;> rfl
  have hP := s8Chk_sound _ _
    (fun y => y < 2 ^ 64 ∧ ∃ w, unpackM y = evalW CFSG.Quasithin.H13.S8Cert.s8G w)
    M (fun j _ => s8GetT_ofT _ _ le_rfl j) s8_step M.tail 1 cs hc List.drop_one fun j hj => by
      rw [Nat.lt_one_iff.mp hj, hhd, h0]
      exact ⟨oneP_lt, [], oneP_eq⟩
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  have := hP j hj
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem s8L_lt : ∀ p ∈ D.s8L, p < 2 ^ 64 :=
  fun y hy => (s8WB_words s8WB_true y (List.mem_reverse.mpr hy)).1

theorem s8L_words : ∀ y ∈ D.s8L, ∃ w, unpackM y = evalW CFSG.Quasithin.H13.S8Cert.s8G w :=
  fun y hy => (s8WB_words s8WB_true y (List.mem_reverse.mpr hy)).2

theorem s8E_eq : CFSG.Quasithin.H13.S8Cert.s8E = D.s8L.map unpackM := by
  rw [CFSG.Quasithin.H13.S8Cert.s8E]

theorem s8E_words : ∀ x ∈ CFSG.Quasithin.H13.S8Cert.s8E,
    ∃ w, x = evalW CFSG.Quasithin.H13.S8Cert.s8G w := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (s8E_eq ▸ hx)
  exact s8L_words y hy

end CertificateChecks.KernelH13

end
