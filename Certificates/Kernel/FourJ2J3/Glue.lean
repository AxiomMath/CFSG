module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02FourData
public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.Sporadic.Schreier.PairJ3Order

public section

namespace CertificateChecks.KernelFourJ2J3

open CFSG.ComponentClassification.Sol76.Sig.GSYard02 CFSG.Sporadic.Schreier

theorem sylowFourJoined_of_card {A : Type} [Group A] {P K : Subgroup A} [Finite P] {k m : ℕ}
    (hm : ¬ 2 ∣ m) (hP : Nat.card P = 2 ^ k * m) (hKP : K ≤ P) (hK : Nat.card K = 2 ^ k)
    (d : FourJoinedData P K) : SylowFourJoined ↥P := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  refine d.sylowFourJoined hKP ?_
  rw [hK, hP, Nat.factorization_mul (pow_ne_zero k two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem sylowFourJoined_j2P_of_data
    {K : Subgroup (Equiv.Perm (Fin 315))} (hKP : K ≤ j2P) (hK : Nat.card K = 128)
    (d : FourJoinedData j2P K) : SylowFourJoined ↥j2P :=
  sylowFourJoined_of_card (k := 7) (m := 4725) (by norm_num) (by rw [card_j2P]; norm_num) hKP
    (by rw [hK]; norm_num) d

theorem sylowFourJoined_j3P_of_data
    {K : Subgroup (Equiv.Perm (Fin 6156))} (hKP : K ≤ j3P) (hK : Nat.card K = 128)
    (d : FourJoinedData j3P K) : SylowFourJoined ↥j3P :=
  sylowFourJoined_of_card (k := 7) (m := 392445) (by norm_num) (by rw [card_j3P]; norm_num) hKP
    (by rw [hK]; norm_num) d

end CertificateChecks.KernelFourJ2J3

end
