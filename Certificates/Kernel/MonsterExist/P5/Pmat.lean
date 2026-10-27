module

public import CFSG.Monster.Existence.StdOdd.P5Inputs

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5

theorem mod_pow_eq_of_digits {c c' : ℕ} :
    ∀ n, (∀ k < n, c / 3 ^ k % 3 = c' / 3 ^ k % 3) → c % 3 ^ n = c' % 3 ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, mod_pow_eq_of_digits n fun k hk => h k (by omega),
      h n (by omega)]

theorem dec_inj {c c' : ℕ} (hc : c < 3 ^ 25) (hc' : c' < 3 ^ 25) (h : dec c = dec c') : c = c' := by
  have hd : ∀ k < 25, c / 3 ^ k % 3 = c' / 3 ^ k % 3 := by
    intro k hk
    have := congrFun (congrFun h ⟨k / 5, by omega⟩) ⟨k % 5, by omega⟩
    have hk5 : 5 * (k / 5) + k % 5 = k := by omega
    simp only [dec, Matrix.of_apply, hk5] at this
    have := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp this
    rwa [Nat.mod_mod, Nat.mod_mod] at this
  have := mod_pow_eq_of_digits 25 hd
  rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this

theorem codes_lt : ∀ i : Fin 81, pcArr.getD i 0 < 3 ^ 25 := by decide +kernel

theorem codes_inj : ∀ i j : Fin 81, pcArr.getD i 0 = pcArr.getD j 0 → i = j := by decide +kernel

theorem pmat_inj : ∀ i j : Fin 81, pmat i = pmat j → i = j := fun i j h =>
  codes_inj i j (dec_inj (codes_lt i) (codes_lt j) h)

end CertificateChecks.MonsterExist.P5

end
