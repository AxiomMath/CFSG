module

public import Certificates.Data.Kernel.LyS0.Check

public section

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0 CFSG.KC.Ord CFSG.KC.Enum

@[expose] noncomputable def regV (A B : Nat) (T : Nat → Nat) (k : Nat) : Nat :=
  nth (regs A B T 745) k

@[expose] noncomputable def findV (k : Nat) (e : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Bool.rec (motive := fun _ => Nat) ih p.2 (Nat.beq p.1 k)) e

@[expose] noncomputable def hasK (k : Nat) (e : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq p.1 k)) e

@[expose] noncomputable def stepE (T : Nat → Nat) (t : Nat) (s : List (Nat × Nat) × Bool) :
    List (Nat × Nat) × Bool :=
  (List.cons (Nat.add t 2, mul (findV (OP T t) s.1) (findV (OQ T t) s.1)) s.1,
    andB s.2 (andB (andB (hasK (OP T t) s.1) (hasK (OQ T t) s.1))
      (andB (Nat.blt (OP T t) (Nat.add t 2)) (Nat.blt (OQ T t) (Nat.add t 2)))))

@[expose] noncomputable def runE (T : Nat → Nat) (t0 : Nat) (s : List (Nat × Nat) × Bool)
    (n : Nat) : List (Nat × Nat) × Bool :=
  Nat.rec (motive := fun _ => List (Nat × Nat) × Bool) s
    (fun i acc => stepE T (Nat.add t0 i) acc) n

@[expose] noncomputable def allIn (o e : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (andB (hasK p.1 e) (Nat.beq (findV p.1 e) p.2)) ih) o

@[expose] noncomputable def pieceK (T : Nat → Nat) (e : List (Nat × Nat)) (t0 n : Nat)
    (o : List (Nat × Nat)) : Bool :=
  andB (Nat.ble (Nat.add t0 n) 745)
    (andB (runE T t0 (e, true) n).2 (allIn o (runE T t0 (e, true) n).1))

@[expose] def Good (A B : Nat) (T : Nat → Nat) (e : List (Nat × Nat)) : Prop :=
  ∀ p ∈ e, regV A B T p.1 = p.2

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem nth_append_lt : ∀ (l : List Nat) (x k : Nat), k < l.length → nth (l ++ [x]) k = nth l k
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | y :: l, x, k + 1, h => by
    change nth (l ++ [x]) k = nth l k
    exact nth_append_lt l x k (by simp only [List.length_cons] at h; omega)

theorem nth_append_len : ∀ (l : List Nat) (x : Nat), nth (l ++ [x]) l.length = x
  | [], _ => rfl
  | y :: l, x => by
    change nth (l ++ [x]) l.length = x
    exact nth_append_len l x

theorem regs_succ (A B : Nat) (T : Nat → Nat) (n : Nat) :
    regs A B T (n + 1) = regs A B T n ++
      [mul (nth (regs A B T n) (OP T n)) (nth (regs A B T n) (OQ T n))] := rfl

theorem regs_len (A B : Nat) (T : Nat → Nat) : ∀ n, (regs A B T n).length = n + 2
  | 0 => rfl
  | n + 1 => by rw [regs_succ, List.length_append, regs_len A B T n]; rfl

theorem nth_regs_mono (A B : Nat) (T : Nat → Nat) (n k : Nat) (hk : k < n + 2) :
    ∀ m, nth (regs A B T (n + m)) k = nth (regs A B T n) k
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, regs_succ, nth_append_lt _ _ _ (by rw [regs_len]; omega)]
    exact nth_regs_mono A B T n k hk m

theorem val_eq (A B : Nat) (T : Nat → Nat) (n k : Nat) (hk : k < n + 2) (hn : n ≤ 745) :
    regV A B T k = nth (regs A B T n) k := by
  unfold regV
  rw [show (745 : Nat) = n + (745 - n) by omega]
  exact nth_regs_mono A B T n k hk (745 - n)

theorem val_zero (A B : Nat) (T : Nat → Nat) : regV A B T 0 = A :=
  val_eq A B T 0 0 (by omega) (by omega)

theorem val_one (A B : Nat) (T : Nat → Nat) : regV A B T 1 = B :=
  val_eq A B T 0 1 (by omega) (by omega)

theorem val_step (A B : Nat) (T : Nat → Nat) (t : Nat) (ht : t < 745) (hp : OP T t < t + 2)
    (hq : OQ T t < t + 2) :
    regV A B T (t + 2) = mul (regV A B T (OP T t)) (regV A B T (OQ T t)) := by
  rw [val_eq A B T (t + 1) (t + 2) (by omega) (by omega), regs_succ,
    val_eq A B T t (OP T t) hp (by omega), val_eq A B T t (OQ T t) hq (by omega)]
  have e := nth_append_len (regs A B T t)
    (mul (nth (regs A B T t) (OP T t)) (nth (regs A B T t) (OQ T t)))
  rw [regs_len] at e
  exact e

theorem findV_good {A B : Nat} {T : Nat → Nat} (k : Nat) :
    ∀ e : List (Nat × Nat), Good A B T e → hasK k e = true → findV k e = regV A B T k
  | [], _, h => by
    change false = true at h
    cases h
  | p :: e, hg, h => by
    cases hb : Nat.beq p.1 k with
    | true =>
      have hk : p.1 = k := Nat.eq_of_beq_eq_true hb
      change Bool.rec (motive := fun _ => Nat) (findV k e) p.2 (Nat.beq p.1 k) = regV A B T k
      rw [hb, ← hk]
      exact (hg p List.mem_cons_self).symm
    | false =>
      change Bool.rec (motive := fun _ => Bool) (hasK k e) true (Nat.beq p.1 k) = true at h
      rw [hb] at h
      change Bool.rec (motive := fun _ => Nat) (findV k e) p.2 (Nat.beq p.1 k) = regV A B T k
      rw [hb]
      exact findV_good k e (fun q hq => hg q (List.mem_cons_of_mem _ hq)) h

theorem runE_good {A B : Nat} {T : Nat → Nat} {t0 : Nat} {e : List (Nat × Nat)}
    (he : Good A B T e) : ∀ n, t0 + n ≤ 745 → (runE T t0 (e, true) n).2 = true →
      Good A B T (runE T t0 (e, true) n).1
  | 0, _, _ => he
  | n + 1, hn, h => by
    change (stepE T (Nat.add t0 n) (runE T t0 (e, true) n)).2 = true at h
    change Good A B T (stepE T (Nat.add t0 n) (runE T t0 (e, true) n)).1
    have e1 : Nat.add t0 n = t0 + n := rfl
    rw [e1] at h ⊢
    obtain ⟨h0, h1⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h1
    obtain ⟨hp, hq⟩ := andB_true h2
    obtain ⟨lp, lq⟩ := andB_true h3
    have ih := runE_good he n (by omega) h0
    have lp' : OP T (t0 + n) < t0 + n + 2 := Nat.le_of_ble_eq_true lp
    have lq' : OQ T (t0 + n) < t0 + n + 2 := Nat.le_of_ble_eq_true lq
    intro p hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · change regV A B T (t0 + n + 2) = mul (findV (OP T (t0 + n)) (runE T t0 (e, true) n).1)
        (findV (OQ T (t0 + n)) (runE T t0 (e, true) n).1)
      rw [findV_good _ _ ih hp, findV_good _ _ ih hq]
      exact val_step A B T (t0 + n) (by omega) lp' lq'
    · exact ih p hp'

theorem allIn_good {A B : Nat} {T : Nat → Nat} {e : List (Nat × Nat)} (he : Good A B T e) :
    ∀ o : List (Nat × Nat), allIn o e = true → Good A B T o
  | [], _ => fun _ hp => absurd hp List.not_mem_nil
  | p :: o, h => by
    change andB (andB (hasK p.1 e) (Nat.beq (findV p.1 e) p.2)) (allIn o e) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨hk, hv⟩ := andB_true h1
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · rw [← findV_good _ _ he hk]
      exact Nat.eq_of_beq_eq_true hv
    · exact allIn_good he o h2 q hq

theorem pieceK_good {A B : Nat} {T : Nat → Nat} {e o : List (Nat × Nat)} {t0 n : Nat}
    (he : Good A B T e) (h : pieceK T e t0 n o = true) : Good A B T o := by
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  exact allIn_good (runE_good he n (Nat.le_of_ble_eq_true h1) h3) o h4

theorem good_start (A B : Nat) (T : Nat → Nat) : Good A B T [(0, A), (1, B)] := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact val_zero A B T
  rcases List.mem_cons.1 hp with rfl | hp
  · exact val_one A B T
  exact absurd hp List.not_mem_nil

theorem good_head {A B : Nat} {T : Nat → Nat} {k v : Nat} {o : List (Nat × Nat)}
    (h : Good A B T ((k, v) :: o)) : regV A B T k = v := h (k, v) List.mem_cons_self

theorem good_tail {A B : Nat} {T : Nat → Nat} {p : Nat × Nat} {o : List (Nat × Nat)}
    (h : Good A B T (p :: o)) : Good A B T o := fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem allBlk_gens {G : Nat → Nat} (R : List Nat) (h0 : nth R 201 = G 0)
    (h1 : nth R 362 = G 1) (h2 : nth R 467 = G 2) (h3 : nth R 637 = G 3)
    (h4 : nth R 746 = G 4) : allBlk 0 (fun j => Nat.beq (nth R (nth gensL j)) (G j)) 5 = true := by
  change bAnd(Nat.beq (nth R 746) (G 4), bAnd(Nat.beq (nth R 637) (G 3), bAnd(
    Nat.beq (nth R 467) (G 2), bAnd(Nat.beq (nth R 362) (G 1), bAnd(
    Nat.beq (nth R 201) (G 0), true))))) = true
  rw [h0, h1, h2, h3, h4, Nat.beq_refl, Nat.beq_refl, Nat.beq_refl, Nat.beq_refl,
    Nat.beq_refl]

theorem strictB_const (y : Nat) (X : Bool) (hX : X = true) : strictB y (fun _ => X) = true := by
  cases y <;> exact hX

theorem gensK_of {A B : Nat} {T G : Nat → Nat} (h0 : regV A B T 201 = G 0)
    (h1 : regV A B T 362 = G 1) (h2 : regV A B T 467 = G 2) (h3 : regV A B T 637 = G 3)
    (h4 : regV A B T 746 = G 4) : gensK A B T G = true :=
  strictB_const _ _ (allBlk_gens (regs A B T 745) h0 h1 h2 h3 h4)

end CertificateChecks.KernelLyS0

end
