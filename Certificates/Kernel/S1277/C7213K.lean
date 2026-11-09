module

public import Certificates.Data.Kernel.S1277K7213

public section

namespace CFSG.KC.C7213K

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm CFSG.KC.C7213

@[expose] noncomputable def wVK (v : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.shiftRight v 1) 21)
    (Nat.shiftLeft (Nat.xor (Nat.land v 21) (Nat.land (Nat.shiftRight v 1) 21)) 1)

@[expose] noncomputable def sVK (c v : ℕ) : ℕ :=
  Nat.xor (Nat.mul v (Nat.mod c 2)) (Nat.mul (wVK v) (Nat.mod (Nat.shiftRight c 1) 2))

@[expose] noncomputable def appK (A : Mc) (v : ℕ) : ℕ :=
  Nat.xor (Nat.xor (sVK (Nat.land v 3) A.c0) (sVK (Nat.land (Nat.shiftRight v 2) 3) A.c1))
    (sVK (Nat.land (Nat.shiftRight v 4) 3) A.c2)

@[expose] noncomputable def mulFK (A B : Mc) : Mc := ⟨appK A B.c0, appK A B.c1, appK A B.c2⟩

@[expose] noncomputable def pwK (A : Mc) (n : ℕ) : Mc → Bool :=
  Nat.rec (motive := fun _ => Mc → Bool) isOne (fun _ r B => forceM (mulFK A B) r) n

@[expose] noncomputable def invCK (c : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) c (nat_lit 2) (Nat.beq c (nat_lit 3))) (nat_lit 3)
    (Nat.beq c (nat_lit 2))

@[expose] noncomputable def pnK (v : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (sVK (invCK (Nat.land v 3)) v)
    (Bool.rec (motive := fun _ => ℕ) (sVK (invCK (Nat.land (Nat.shiftRight v 2) 3)) v)
      (sVK (invCK (Nat.land (Nat.shiftRight v 4) 3)) v)
      (Nat.beq (Nat.land (Nat.shiftRight v 2) 3) 0))
    (Nat.beq (Nat.land v 3) 0)

@[expose] noncomputable def memO (q : ℕ) : Bool :=
  orB (Nat.beq q 1) (orB (Nat.beq q 4) (orB (Nat.beq q 16) (orB (Nat.beq q 21)
    (orB (Nat.beq q 57) (Nat.beq q 45)))))

@[expose] noncomputable def neB (a b : ℕ) : Bool := notB (Nat.beq a b)

@[expose] noncomputable def gmK (q1 q2 q3 q4 q5 q6 : ℕ) : Bool :=
  andB (andB (memO q1) (andB (memO q2) (andB (memO q3) (andB (memO q4)
      (andB (memO q5) (memO q6))))))
    (andB (andB (neB q1 q2) (andB (neB q1 q3) (andB (neB q1 q4) (andB (neB q1 q5) (neB q1 q6)))))
      (andB (andB (neB q2 q3) (andB (neB q2 q4) (andB (neB q2 q5) (neB q2 q6))))
        (andB (andB (neB q3 q4) (andB (neB q3 q5) (neB q3 q6)))
          (andB (andB (neB q4 q5) (neB q4 q6)) (neB q5 q6)))))

@[expose] noncomputable def inGmK (A : Mc) : Bool :=
  strictB (pnK (appK A 1)) fun q1 => strictB (pnK (appK A 4)) fun q2 =>
  strictB (pnK (appK A 16)) fun q3 => strictB (pnK (appK A 21)) fun q4 =>
  strictB (pnK (appK A 57)) fun q5 => strictB (pnK (appK A 45)) fun q6 =>
    gmK q1 q2 q3 q4 q5 q6

@[expose] noncomputable def memSK (s i : ℕ) : Bool :=
  andB (Nat.blt i 262144) (Nat.beq (Nat.land (Nat.shiftRight s (Nat.add i 64)) 1) 1)

@[expose] noncomputable def eltKK (n : ℕ) : Bool :=
  andB (inGmK (Mc.ofIdx n)) (pwK (Mc.ofIdx n) (nat_lit 60) Mc.one)

@[expose] noncomputable def colKK (s : ℕ) : Bool :=
  allL (fun a => allL (fun b => allL (fun c =>
    orB (notB (inGmK ⟨a, b, c⟩)) (memSK s (mcIdx ⟨a, b, c⟩))) v18) v18) v18

@[expose] noncomputable def chk7213K (L : List ℕ) : Bool :=
  andB (ndK L 0) (andB (allL eltKK L) (strictB (setK L 0) colKK))

theorem strictB_eqK (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem andB_eqK (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eqK (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eqK (a : Bool) : notB a = !a := by cases a <;> rfl

theorem mul_mod_two_eqK (x n : ℕ) : x * (n % 2) = if n % 2 = 1 then x else 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem sVK_eq (c v : ℕ) : sVK c v = sV c v := by
  change v * (c % 2) ^^^ wV v * ((c >>> 1) % 2) = sV c v
  rw [sV, mul_mod_two_eqK, mul_mod_two_eqK]

theorem appK_eq (A : Mc) (v : ℕ) : appK A v = A.app v := by
  simp only [appK, Mc.app, sVK_eq]
  rfl

theorem mulFK_eq : mulFK = mulF := by
  funext A B
  rfl

theorem pwK_eq : pwK = pw := by
  funext A n
  unfold pwK pw
  rw [mulFK_eq]

theorem beq_false_ofK {a b : ℕ} (h : ¬a = b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem invCK_eq (c : ℕ) : invCK c = invC c := by
  unfold invCK invC
  by_cases h2 : c = 2
  · subst h2; rfl
  · by_cases h3 : c = 3
    · subst h3; rfl
    · rw [beq_false_ofK h2, beq_false_ofK h3, if_neg h2, if_neg h3]

theorem pnK_eq (v : ℕ) : pnK v = pn v := by
  unfold pnK pn
  simp only [sVK_eq, invCK_eq]
  have e1 : Nat.land v 3 = v &&& 3 := rfl
  have e2 : Nat.land (Nat.shiftRight v 2) 3 = (v >>> 2) &&& 3 := rfl
  have e3 : Nat.land (Nat.shiftRight v 4) 3 = (v >>> 4) &&& 3 := rfl
  rw [e1, e2, e3]
  by_cases h1 : v &&& 3 = 0
  · have b1 : Nat.beq (v &&& 3) 0 = true := Nat.beq_eq_true_eq _ _ ▸ h1
    rw [b1, if_neg (fun h => h h1)]
    by_cases h2 : (v >>> 2) &&& 3 = 0
    · have b2 : Nat.beq ((v >>> 2) &&& 3) 0 = true := Nat.beq_eq_true_eq _ _ ▸ h2
      rw [b2, if_neg (fun h => h h2)]
    · rw [beq_false_ofK h2, if_pos h2]
  · rw [beq_false_ofK h1, if_pos h1]

theorem beqBK (a b : ℕ) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b <;> cases h' : (a == b) <;> simp_all [Nat.beq_eq]

theorem gmK_eq (q1 q2 q3 q4 q5 q6 : ℕ) : gmK q1 q2 q3 q4 q5 q6 =
    (([q1, q2, q3, q4, q5, q6].all fun q => oPts.contains q) &&
      decide [q1, q2, q3, q4, q5, q6].Nodup) := by
  unfold gmK memO neB oPts
  simp only [andB_eqK, orB_eqK, notB_eqK, beqBK]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    List.all_cons, List.all_nil, List.contains_cons, List.contains_nil, decide_eq_true_eq,
    List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, Bool.and_true, Bool.or_false,
    not_or, or_false, not_false_eq_true, and_true, ne_eq]

theorem inGmK_eq : inGmK = inGm := by
  funext A
  unfold inGmK inGm
  simp only [strictB_eqK, pnK_eq, appK_eq, gmK_eq]
  rfl

theorem memSK_eq : memSK = memS := by
  funext s i
  unfold memSK memS
  rw [andB_eqK]
  have h1 : Nat.blt i 262144 = decide (i < 262144) := by
    cases h : Nat.blt i 262144
    · exact (decide_eq_false (fun h' => by
        rw [← Nat.blt_eq] at h'; rw [h'] at h; exact Bool.noConfusion h)).symm
    · exact (decide_eq_true (by rw [← Nat.blt_eq]; exact h)).symm
  have h2 : Nat.beq (Nat.land (Nat.shiftRight s (Nat.add i 64)) 1) 1 = s.testBit (i + 64) := by
    rw [show Nat.land (Nat.shiftRight s (Nat.add i 64)) 1 = (s >>> (i + 64)) % 2 from
      Nat.and_one_is_mod _, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ (i + 64)) with h | h <;> rw [h] <;> rfl
  rw [h1, h2]

theorem chk7213_eqK : chk7213 = chk7213K := by
  funext L
  unfold chk7213 chk7213K eltK eltKK colK colKK
  rw [inGmK_eq, memSK_eq, pwK_eq]

end CFSG.KC.C7213K

end
