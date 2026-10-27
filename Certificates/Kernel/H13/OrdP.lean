module

public import Certificates.Kernel.H13.PowP

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P

@[expose] def ord8Go (e X : ℕ) (n : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ r acc k => Bool.rec (r (mulP X acc) (Nat.add k 1)) (Nat.beq (Nat.mod e k) 0)
      (Nat.beq acc oneP)) n

@[expose] def ord8B (e X : ℕ) : Bool := ord8Go e X e (mulP X oneP) 1

theorem ord8Go_sound (e X : ℕ) : ∀ n acc k, acc = powP X k → ord8Go e X n acc k = true →
    ∃ m, powP X m = oneP ∧ e % m = 0
  | 0, _, _, _, h => by simp [ord8Go] at h
  | n + 1, acc, k, hacc, h => by
    have h' : Bool.rec (ord8Go e X n (mulP X acc) (k + 1)) (Nat.beq (e % k) 0)
        (Nat.beq acc oneP) = true := h
    cases hb : Nat.beq acc oneP
    · rw [hb] at h'
      exact ord8Go_sound e X n _ (k + 1) (by rw [hacc]; rfl) h'
    · rw [hb] at h'
      exact ⟨k, hacc ▸ Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true h'⟩

theorem pow8_eq_map (x : List ℕ) : ∀ k,
    CFSG.Quasithin.H13.O3Cert.pow8 x k = one8.map (mv8 x)^[k]
  | 0 => by rw [CFSG.Quasithin.H13.O3Cert.pow8, Function.iterate_zero, List.map_id]
  | k + 1 => by
    rw [CFSG.Quasithin.H13.O3Cert.pow8, pow8_eq_map x k, mul8, List.map_map,
      Function.iterate_succ']

theorem pow8_mul_of_eq_one (x : List ℕ) (m q : ℕ)
    (h : CFSG.Quasithin.H13.O3Cert.pow8 x m = one8) :
    CFSG.Quasithin.H13.O3Cert.pow8 x (m * q) = one8 := by
  rw [pow8_eq_map] at h ⊢
  simp only [one8, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [Function.iterate_mul, Function.iterate_fixed h0, Function.iterate_fixed h1,
    Function.iterate_fixed h2, Function.iterate_fixed h3, Function.iterate_fixed h4,
    Function.iterate_fixed h5, Function.iterate_fixed h6, Function.iterate_fixed h7, and_self]

theorem pow8_of_ord8B {e X : ℕ} (h : ord8B e X = true) :
    CFSG.Quasithin.H13.O3Cert.pow8 (unpackM X) e = one8 := by
  obtain ⟨m, hm, he⟩ := ord8Go_sound e X e (mulP X oneP) 1 rfl h
  have hm8 : CFSG.Quasithin.H13.O3Cert.pow8 (unpackM X) m = one8 := by
    rw [pow8_unpackM, hm, oneP_eq]
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero he
  exact pow8_mul_of_eq_one _ m q hm8

theorem all_pow8_of_ord8B (e : ℕ) (L : List ℕ) (h : L.all (ord8B e) = true) :
    (L.map unpackM).all (fun x => CFSG.Quasithin.H13.O3Cert.pow8 x e == one8) = true := by
  rw [List.all_map, List.all_eq_true]
  intro X hX
  rw [List.all_eq_true] at h
  simp [pow8_of_ord8B (h X hX)]

end CertificateChecks.KernelH13

end
