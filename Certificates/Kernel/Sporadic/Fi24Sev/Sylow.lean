module

public import Certificates.Kernel.Sporadic.Fi24Sev.SevenB
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.KD.Fi24Sev.Sylow

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (J)
open CFSG.KD.Fi24ThreeO.Group CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] {x y c : G}

def ConjYC (y c g : G) : Prop := ∃ t : G, t * g * t⁻¹ = y ∨ t * g * t⁻¹ = c

theorem conjYC_of_semiconj {h g g' : G} (hs : h * g = g' * h) (hP : ConjYC y c g') :
    ConjYC y c g := by
  obtain ⟨t, ht⟩ := hP
  refine ⟨t * h, ?_⟩
  have e : t * h * g * (t * h)⁻¹ = t * g' * t⁻¹ := by
    calc t * h * g * (t * h)⁻¹ = t * (h * g) * h⁻¹ * t⁻¹ := by group
      _ = t * (g' * h) * h⁻¹ * t⁻¹ := by rw [hs]
      _ = t * g' * t⁻¹ := by group
  rw [e]
  exact ht

theorem inv_conj_pow (t g : G) : ∀ n : ℕ, (t⁻¹ * g * t) ^ n = t⁻¹ * g ^ n * t
  | 0 => by simp
  | n + 1 => by rw [pow_succ, inv_conj_pow t g n, pow_succ]; group

theorem conjYC_of_rep {M g : G} (r : G) (hr : r = y ∨ r = c) (hs : M * g = r * M) :
    ConjYC y c g := by
  refine conjYC_of_semiconj hs ⟨1, ?_⟩
  simpa using hr

theorem conjYC_pow {r M : G} (hr7 : r ^ 7 = 1) (hM : M * r ^ 3 = r * M) (hP : ConjYC y c r) :
    ∀ m, m % 7 ≠ 0 → ConjYC y c (r ^ m) := by
  have h3 : ∀ n, ConjYC y c (r ^ (3 ^ n)) := by
    intro n
    induction n with
    | zero => simpa using hP
    | succ n ih =>
      have hs : SemiconjBy M (r ^ 3) r := hM
      have h2 := hs.pow_right (3 ^ n)
      rw [← pow_mul, ← pow_succ'] at h2
      exact conjYC_of_semiconj h2 ih
  intro m hm
  have key : ∀ m' < 7, m' ≠ 0 → ∃ n < 6, 3 ^ n % 7 = m' := by decide
  obtain ⟨n, -, hn⟩ := key (m % 7) (Nat.mod_lt _ (by norm_num)) hm
  rw [pow_eq_pow_mod m hr7, ← hn, ← pow_eq_pow_mod _ hr7]
  exact h3 n

variable (hx : x ^ 7 = 1) (hy : y ^ 7 = 1) (hc : c = x * y * x ^ 6 * y ^ 6) (hcx : c * x = x * c)
  (hcy : c * y = y * c)
include hx hy hc

theorem comm_eq : ⁅x, y⁆ = c := by
  have hx6 : x ^ 6 = x⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx]
  have hy6 : y ^ 6 = y⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hy]
  rw [hc, hx6, hy6, commutatorElement_def]

include hcx in
theorem c_pow_seven : c ^ 7 = 1 := by
  have hz : Commute ⁅x, y⁆ x := by rw [comm_eq hx hy hc]; exact hcx
  rw [← comm_eq hx hy hc, CFSG.SectionRank.LocalWitness.commutator_pow_eq hz, hx,
    commutatorElement_one_left]

include hcx hcy

theorem xy_eq : x * y = y * x * c := by
  have hc' : c = x * y * x⁻¹ * y⁻¹ := by rw [← commutatorElement_def, comm_eq hx hy hc]
  calc x * y = c * y * x := by rw [hc']; group
    _ = y * c * x := by rw [hcy]
    _ = y * x * c := by rw [mul_assoc, hcx, ← mul_assoc]

theorem yx_eq : y * x = x * y * c ^ 6 := by
  calc y * x = y * x * c ^ 7 := by rw [c_pow_seven hx hy hc hcx, mul_one]
    _ = (y * x * c) * c ^ 6 := by rw [pow_succ']; group
    _ = x * y * c ^ 6 := by rw [← xy_eq hx hy hc hcx hcy]

theorem ypow_x (b : ℕ) : y ^ b * x = x * y ^ b * c ^ (6 * b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hc6 : Commute (c ^ 6) (y ^ b) := (Commute.pow_pow hcy 6 b)
    calc y ^ (b + 1) * x = y * (y ^ b * x) := by rw [pow_succ', mul_assoc]
      _ = (y * x) * y ^ b * c ^ (6 * b) := by rw [ih]; simp only [mul_assoc]
      _ = x * y * (c ^ 6 * y ^ b) * c ^ (6 * b) := by
        rw [yx_eq hx hy hc hcx hcy]; simp only [mul_assoc]
      _ = x * y * (y ^ b * c ^ 6) * c ^ (6 * b) := by rw [hc6.eq]
      _ = x * y ^ (b + 1) * c ^ (6 * (b + 1)) := by
        rw [pow_succ' y b, show 6 * (b + 1) = 6 + 6 * b by ring, pow_add]
        simp only [mul_assoc]

theorem ypow_xpow (a b : ℕ) : y ^ b * x ^ a = x ^ a * y ^ b * c ^ (6 * a * b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hcx' : Commute (c ^ (6 * a * b)) x := Commute.pow_left hcx _
    calc y ^ b * x ^ (a + 1) = (y ^ b * x ^ a) * x := by rw [pow_succ, mul_assoc]
      _ = x ^ a * y ^ b * (c ^ (6 * a * b) * x) := by rw [ih]; simp only [mul_assoc]
      _ = x ^ a * y ^ b * (x * c ^ (6 * a * b)) := by rw [hcx'.eq]
      _ = x ^ a * (y ^ b * x) * c ^ (6 * a * b) := by simp only [mul_assoc]
      _ = x ^ a * (x * y ^ b * c ^ (6 * b)) * c ^ (6 * a * b) := by rw [ypow_x hx hy hc hcx hcy]
      _ = x ^ (a + 1) * y ^ b * c ^ (6 * (a + 1) * b) := by
        rw [pow_succ x a, show 6 * (a + 1) * b = 6 * b + 6 * a * b by ring, pow_add]
        simp only [mul_assoc]

theorem x_ypow (b : ℕ) : x * y ^ b = y ^ b * x * c ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hcb : Commute (c ^ b) y := Commute.pow_left hcy _
    calc x * y ^ (b + 1) = (x * y ^ b) * y := by rw [pow_succ, mul_assoc]
      _ = y ^ b * x * (c ^ b * y) := by rw [ih]; simp only [mul_assoc]
      _ = y ^ b * x * (y * c ^ b) := by rw [hcb.eq]
      _ = y ^ b * (x * y) * c ^ b := by simp only [mul_assoc]
      _ = y ^ b * (y * x * c) * c ^ b := by rw [xy_eq hx hy hc hcx hcy]
      _ = y ^ (b + 1) * x * c ^ (b + 1) := by
        rw [pow_succ y b, pow_succ' c b]; simp only [mul_assoc]

theorem xpow_ypow (a b : ℕ) : x ^ a * y ^ b = y ^ b * x ^ a * c ^ (a * b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hcx' : Commute (c ^ b) (x ^ a) := Commute.pow_pow hcx b a
    calc x ^ (a + 1) * y ^ b = x * (x ^ a * y ^ b) := by rw [pow_succ', mul_assoc]
      _ = (x * y ^ b) * x ^ a * c ^ (a * b) := by rw [ih]; simp only [mul_assoc]
      _ = y ^ b * x * (c ^ b * x ^ a) * c ^ (a * b) := by
        rw [x_ypow hx hy hc hcx hcy]; simp only [mul_assoc]
      _ = y ^ b * x * (x ^ a * c ^ b) * c ^ (a * b) := by rw [hcx'.eq]
      _ = y ^ b * x ^ (a + 1) * c ^ ((a + 1) * b) := by
        rw [pow_succ' x a, show (a + 1) * b = b + a * b by ring, pow_add]
        simp only [mul_assoc]

theorem ypow_conj (b i j k : ℕ) :
    y ^ b * (x ^ i * y ^ j * c ^ k) = (x ^ i * y ^ j * c ^ (k + 6 * i * b)) * y ^ b := by
  have e1 := ypow_xpow hx hy hc hcx hcy i b
  have hcm : Commute (c ^ (6 * i * b)) (y ^ j) := Commute.pow_pow hcy _ _
  have hcm' : Commute (c ^ (k + 6 * i * b)) (y ^ b) := Commute.pow_pow hcy _ _
  calc y ^ b * (x ^ i * y ^ j * c ^ k) = (y ^ b * x ^ i) * y ^ j * c ^ k := by
        simp only [mul_assoc]
    _ = x ^ i * y ^ b * (c ^ (6 * i * b) * y ^ j) * c ^ k := by rw [e1]; simp only [mul_assoc]
    _ = x ^ i * y ^ b * (y ^ j * c ^ (6 * i * b)) * c ^ k := by rw [hcm.eq]
    _ = x ^ i * (y ^ b * y ^ j) * (c ^ (6 * i * b) * c ^ k) := by simp only [mul_assoc]
    _ = x ^ i * (y ^ j * y ^ b) * (c ^ k * c ^ (6 * i * b)) := by
        rw [(Commute.pow_pow_self y b j).eq, (Commute.pow_pow_self c (6 * i * b) k).eq]
    _ = x ^ i * y ^ j * (y ^ b * c ^ (k + 6 * i * b)) := by rw [pow_add]; simp only [mul_assoc]
    _ = x ^ i * y ^ j * c ^ (k + 6 * i * b) * y ^ b := by rw [← hcm'.eq]; simp only [mul_assoc]

theorem xpow_conj (a j k : ℕ) :
    x ^ a * (y ^ j * c ^ k) = (y ^ j * c ^ (k + a * j)) * x ^ a := by
  have e1 := xpow_ypow hx hy hc hcx hcy a j
  have hca : Commute (c ^ (k + a * j)) (x ^ a) := Commute.pow_pow hcx _ _
  have hck : Commute (c ^ (a * j)) (c ^ k) := Commute.pow_pow_self c _ _
  calc x ^ a * (y ^ j * c ^ k) = (x ^ a * y ^ j) * c ^ k := by rw [mul_assoc]
    _ = y ^ j * (x ^ a * (c ^ (a * j) * c ^ k)) := by rw [e1]; simp only [mul_assoc]
    _ = y ^ j * (x ^ a * c ^ (k + a * j)) := by rw [hck.eq, ← pow_add]
    _ = y ^ j * c ^ (k + a * j) * x ^ a := by rw [← hca.eq, mul_assoc]

theorem xy_pow (lam : ℕ) : ∀ n : ℕ, ∃ e : ℕ, (x * y ^ lam) ^ n = x ^ n * y ^ (n * lam) * c ^ e := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨6 * 1 * (n * lam) + e, ?_⟩
    have hy1 := ypow_xpow hx hy hc hcx hcy 1 (n * lam)
    rw [pow_one] at hy1
    have hce : Commute (c ^ e) x := Commute.pow_left hcx _
    have hce' : Commute (c ^ e) (y ^ lam) := Commute.pow_pow hcy _ _
    have hcf : Commute (c ^ (6 * 1 * (n * lam))) (y ^ lam) := Commute.pow_pow hcy _ _
    calc (x * y ^ lam) ^ (n + 1) = x ^ n * y ^ (n * lam) * (c ^ e * x) * y ^ lam := by
          rw [pow_succ, he]; simp only [mul_assoc]
      _ = x ^ n * (y ^ (n * lam) * x) * (c ^ e * y ^ lam) := by
          rw [hce.eq]; simp only [mul_assoc]
      _ = x ^ n * (x * y ^ (n * lam) * c ^ (6 * 1 * (n * lam))) * (y ^ lam * c ^ e) := by
          rw [hy1, hce'.eq]
      _ = x ^ n * x * y ^ (n * lam) * (c ^ (6 * 1 * (n * lam)) * y ^ lam) * c ^ e := by
          simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ ((n + 1) * lam) * c ^ (6 * 1 * (n * lam) + e) := by
          rw [hcf.eq, ← pow_succ, show (n + 1) * lam = n * lam + lam by ring, pow_add y, pow_add c]
          simp only [mul_assoc]

theorem inj_of (hc1 : c ≠ 1) : ∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 →
    k' < 7 → x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k' := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ho : orderOf c = 7 := orderOf_eq_prime (c_pow_seven hx hy hc hcx) hc1
  have hceq : ∀ a b : ℕ, a < 7 → b < 7 → c ^ a = c ^ b → a = b := by
    intro a b ha hb h
    rw [pow_eq_pow_iff_modEq, ho, Nat.ModEq] at h
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
    exact h
  intro i j k i' j' k' hi hj hk hi' hj' hk' h
  have ey : ∀ a b d : ℕ, x ^ a * y ^ b * c ^ (d + 6 * a * 1) =
      (x ^ a * y ^ b * c ^ d) * c ^ (6 * a * 1) := by
    intro a b d
    rw [pow_add]
    simp only [mul_assoc]
  have h1 := ypow_conj hx hy hc hcx hcy 1 i j k
  have h2 := ypow_conj hx hy hc hcx hcy 1 i' j' k'
  rw [ey] at h1 h2
  rw [h] at h1
  have h3 : c ^ (6 * i * 1) = c ^ (6 * i' * 1) :=
    mul_left_cancel (mul_right_cancel (h1.symm.trans h2))
  have hii : i = i' := by
    have e1 : c ^ (6 * i * 1) = c ^ (6 * i * 1 % 7) := pow_eq_pow_mod _ (c_pow_seven hx hy hc hcx)
    have e2 : c ^ (6 * i' * 1) = c ^ (6 * i' * 1 % 7) :=
      pow_eq_pow_mod _ (c_pow_seven hx hy hc hcx)
    rw [e1, e2] at h3
    have := hceq _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h3
    omega
  subst hii
  have hb : y ^ j * c ^ k = y ^ j' * c ^ k' := by
    have h' := h
    simp only [mul_assoc] at h'
    exact mul_left_cancel h'
  have ex : ∀ b d : ℕ, y ^ b * c ^ (d + 1 * b) = (y ^ b * c ^ d) * c ^ (1 * b) := by
    intro b d
    rw [pow_add]
    simp only [mul_assoc]
  have g1 := xpow_conj hx hy hc hcx hcy 1 j k
  have g2 := xpow_conj hx hy hc hcx hcy 1 j' k'
  rw [ex] at g1 g2
  rw [hb] at g1
  have g3 : c ^ (1 * j) = c ^ (1 * j') :=
    mul_left_cancel (mul_right_cancel (g1.symm.trans g2))
  have hjj : j = j' := hceq _ _ (by omega) (by omega) (by simpa using g3)
  subst hjj
  exact ⟨rfl, rfl, hceq _ _ hk hk' (mul_left_cancel hb)⟩

theorem cube_conjYC (hY : ∀ m, m % 7 ≠ 0 → ConjYC y c (y ^ m))
    (hC : ∀ m, m % 7 ≠ 0 → ConjYC y c (c ^ m)) (hW : ∀ lam < 7, ConjYC y c (x * y ^ lam)) :
    ∀ i j k : ℕ, i < 7 → j < 7 → k < 7 → i + j + k ≠ 0 → ConjYC y c (x ^ i * y ^ j * c ^ k) := by
  have hc7 := c_pow_seven hx hy hc hcx
  intro i j k hi hj hk hijk
  by_cases hi0 : i = 0
  · subst hi0
    rw [pow_zero, one_mul]
    by_cases hj0 : j = 0
    · subst hj0
      rw [pow_zero, one_mul]
      exact hC k (by omega)
    · have key : ∀ j < 7, j ≠ 0 → ∀ k < 7, ∃ a < 7, (k + a * j) % 7 = 0 := by decide
      obtain ⟨a, -, ha⟩ := key j hj hj0 k hk
      have hs := xpow_conj hx hy hc hcx hcy a j k
      rw [pow_eq_pow_mod (k + a * j) hc7, ha, pow_zero, mul_one] at hs
      exact conjYC_of_semiconj hs (hY j (by omega))
  · have key : ∀ i < 7, i ≠ 0 → ∀ j < 7, ∃ lam < 7, i * lam % 7 = j := by decide
    obtain ⟨lam, hlam, hl⟩ := key i hi hi0 j hj
    obtain ⟨t, ht⟩ := hW lam hlam
    have hwi : ConjYC y c ((x * y ^ lam) ^ i) := by
      have hs : t * (x * y ^ lam) ^ i = (t * (x * y ^ lam) * t⁻¹) ^ i * t := by
        rw [conj_pow]; group
      rcases ht with ht | ht
      · rw [ht] at hs
        exact conjYC_of_semiconj hs (hY i (by omega))
      · rw [ht] at hs
        exact conjYC_of_semiconj hs (hC i (by omega))
    obtain ⟨e, he⟩ := xy_pow hx hy hc hcx hcy lam i
    rw [pow_eq_pow_mod (i * lam) hy, hl] at he
    have key2 : ∀ i < 7, i ≠ 0 → ∀ k < 7, ∀ e' < 7, ∃ b < 7, (k + 6 * i * b) % 7 = e' := by decide
    obtain ⟨b, -, hb⟩ := key2 i hi hi0 k hk (e % 7) (Nat.mod_lt _ (by norm_num))
    have hs := ypow_conj hx hy hc hcx hcy b i j k
    rw [pow_eq_pow_mod (k + 6 * i * b) hc7, hb, ← pow_eq_pow_mod e hc7, ← he] at hs
    exact conjYC_of_semiconj hs hwi

end Generic

open CFSG.KD.Fi24Sev.SevenB


instance : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)

theorem factorization_card_J : (Nat.card J).factorization 7 = 3 := by
  rw [CFSG.Sporadic.Fi24.card_J,
    show (1255205709190661721292800 : ℕ) = 7 ^ 3 * 3659491863529626009600 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem conj_fst {t r : ℕ} (h : ∃ e ∈ CFSG.KD.Fi24SevB.cj, e.1 = t ∧ e.2.1 = r) :
    (fi24SevenData.conj[t]!).1 = r := by
  obtain ⟨e, he, h1, h2⟩ := h
  obtain ⟨hlt, hC7, -⟩ := cj_data e he
  have hconj : fi24SevenData.conj[e.1]! = (e.2.1, e.2.2.1) := by
    rw [CertificateChecks.KernelF24S.conj_eq, ← hC7,
      getElem!_pos _ e.1 (by simp [CertificateChecks.KernelF24S.c7_len]; omega)]
    simp only [List.getElem_toArray]
    rw [List.getD_eq_getElem _ _ (by rw [CertificateChecks.KernelF24S.c7_len]; omega)]
  rw [← h1, hconj, h2]

theorem conj3 : (fi24SevenData.conj[3]!).1 = 1 := conj_fst (by decide +kernel)

theorem conj21 : (fi24SevenData.conj[21]!).1 = 0 := conj_fst (by decide +kernel)

variable (hB : Bridge)
include hB

theorem inj : ∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 → k' < 7 →
    sev 64 ^ i * sev 66 ^ j * sev 67 ^ k = sev 64 ^ i' * sev 66 ^ j' * sev 67 ^ k' →
    i = i' ∧ j = j' ∧ k = k' := by
  obtain ⟨hx, hy, hc, hcx, hcy, hc1⟩ := cube_facts hB
  exact inj_of hx hy hc hcx hcy hc1

theorem cube_conj : ∀ i j k : ℕ, i < 7 → j < 7 → k < 7 → i + j + k ≠ 0 →
    ConjYC (sev 66) (sev 67) (sev 64 ^ i * sev 66 ^ j * sev 67 ^ k) := by
  obtain ⟨hx, hy, hc, hcx, hcy, hc1⟩ := cube_facts hB
  have hc7 := c_pow_seven hx hy hc hcx
  have hyY : ConjYC (sev 66) (sev 67) (sev 66) := ⟨1, Or.inl (by group)⟩
  have hcC' : ConjYC (sev 66) (sev 67) (sev 67) := ⟨1, Or.inr (by group)⟩
  have hM3 := conj_facts hB (t := 3) (by decide)
  have hM21 := conj_facts hB (t := 21) (by decide)
  rw [conj3, if_neg (by decide)] at hM3
  rw [conj21, if_pos (by decide)] at hM21
  have e3 : cube7 3 = sev 67 ^ 3 := by simp [cube7]
  have e21 : cube7 21 = sev 66 ^ 3 := by simp [cube7]
  rw [e3] at hM3
  rw [e21] at hM21
  refine cube_conjYC hx hy hc hcx hcy (conjYC_pow hy hM21 hyY) (conjYC_pow hc7 hM3 hcC')
    (fun lam hlam => ?_)
  have ht : 49 + 7 * lam ∈ [3, 21, 49, 56, 63, 70, 77, 84, 91] := by
    interval_cases lam <;> decide
  have hM := conj_facts hB ht
  have e : cube7 (49 + 7 * lam) = sev 64 * sev 66 ^ lam := by
    simp only [cube7]
    rw [show (49 + 7 * lam) / 49 = 1 by omega, show (49 + 7 * lam) / 7 % 7 = lam by omega,
      show (49 + 7 * lam) % 7 = 0 by omega, pow_one, pow_zero, mul_one]
  rw [e] at hM
  refine conjYC_of_rep _ ?_ hM
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem card_Q : Nat.card (Subgroup.closure ({sev 64, sev 66} : Set J)) = 7 ^ 3 := by
  obtain ⟨hx, hy, hc, hcx, hcy, hc1⟩ := cube_facts hB
  have hxy := comm_eq hx hy hc
  refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube (by norm_num) hx hy
    (by rw [hxy]; exact hcx) (by rw [hxy]; exact hcy) ?_
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  simp only [hxy] at h
  obtain ⟨h1, h2, h3⟩ := inj hB i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
  exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))

theorem exists_conj_mem_Q {g : J} (hg : IsPGroup 7 (Subgroup.zpowers g)) :
    ∃ t : J, t⁻¹ * g * t ∈ Subgroup.closure ({sev 64, sev 66} : Set J) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S0 : Sylow 7 J := Sylow.ofCard (Subgroup.closure ({sev 64, sev 66} : Set J))
    (by rw [card_Q hB, factorization_card_J])
  obtain ⟨S, hS⟩ := hg.exists_le_sylow
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq J S0 S
  have hmem : g ∈ ((t • S0 : Sylow 7 J) : Subgroup J) := by
    rw [ht]
    exact hS (Subgroup.mem_zpowers g)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  exact ⟨t, hmem⟩

theorem mem_Q_conj {h : J} (hh : h ∈ Subgroup.closure ({sev 64, sev 66} : Set J)) :
    h = 1 ∨ ConjYC (sev 66) (sev 67) h := by
  obtain ⟨hx, hy, hc, hcx, hcy, hc1⟩ := cube_facts hB
  have hxy := comm_eq hx hy hc
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := CFSG.SectionRank.LocalWitness.mem_closure_normalForm
    (by norm_num) hx hy (by rw [hxy]; exact hcx) (by rw [hxy]; exact hcy) hh
  rw [hxy]
  by_cases h0 : i + j + k = 0
  · left
    rw [show i = 0 by omega, show j = 0 by omega, show k = 0 by omega]
    simp
  · exact Or.inr (cube_conj hB i j k hi hj hk h0)

theorem conj : ∀ s : J, orderOf s = 7 → ∃ t : J, t * s * t⁻¹ = sev 66 ∨ t * s * t⁻¹ = sev 67 := by
  intro s hs
  have hp : IsPGroup 7 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨t, ht⟩ := exists_conj_mem_Q hB hp
  rcases mem_Q_conj hB ht with h1 | h1
  · exfalso
    have : s = 1 := by
      calc s = t * (t⁻¹ * s * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hs
    omega
  · exact conjYC_of_semiconj (h := t⁻¹) (g' := t⁻¹ * s * t) (by group) h1

theorem pow_seven {g : J} (hg : g ^ 49 = 1) : g ^ 7 = 1 := by
  obtain ⟨hx, hy, hc, hcx, hcy, hc1⟩ := cube_facts hB
  have hc7 := c_pow_seven hx hy hc hcx
  have hp : IsPGroup 7 (Subgroup.zpowers g) := by
    have hd : orderOf g ∣ 7 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hg)
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow (by norm_num)).1 hd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  obtain ⟨t, ht⟩ := exists_conj_mem_Q hB hp
  have h7 : (t⁻¹ * g * t) ^ 7 = 1 := by
    rcases mem_Q_conj hB ht with h1 | ⟨u, hu⟩
    · rw [h1, one_pow]
    · have e : u * (t⁻¹ * g * t) ^ 7 * u⁻¹ = (u * (t⁻¹ * g * t) * u⁻¹) ^ 7 := by rw [conj_pow]
      have h1 : u * (t⁻¹ * g * t) ^ 7 * u⁻¹ = 1 := by
        rw [e]
        rcases hu with hu | hu
        · rw [hu, hy]
        · rw [hu, hc7]
      calc (t⁻¹ * g * t) ^ 7 = u⁻¹ * (u * (t⁻¹ * g * t) ^ 7 * u⁻¹) * u := by group
        _ = 1 := by rw [h1]; group
  rw [inv_conj_pow] at h7
  calc g ^ 7 = t * (t⁻¹ * g ^ 7 * t) * t⁻¹ := by group
    _ = 1 := by rw [h7]; group

end CFSG.KD.Fi24Sev.Sylow

end
