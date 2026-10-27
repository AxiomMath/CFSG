module

public import Certificates.Data.ParrottPSp43

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946.Alg

open CFSG.RankThree.GF2n.Parrott

theorem t_sq : t * t = 1 := by decide +kernel
theorem t_ne_one : t ≠ 1 := by decide +kernel
theorem u_sq : u * u = 1 := by decide +kernel
theorem u_ne_one : u ≠ 1 := by decide +kernel
theorem v_sq : v * v = 1 := by decide +kernel
theorem v_ne_one : v ≠ 1 := by decide +kernel
theorem sigma1_cube : sigma1 ^ 3 = 1 := by decide +kernel
theorem sigma1_ne_one : sigma1 ≠ 1 := by decide +kernel
theorem sigma2_cube : sigma2 ^ 3 = 1 := by decide +kernel
theorem sigma2_ne_one : sigma2 ≠ 1 := by decide +kernel
theorem alpha1_sq : alpha1 * alpha1 = t := by decide +kernel
theorem alpha1_ne_one : alpha1 ≠ 1 := by decide +kernel
theorem alpha1_pow_four : alpha1 ^ 4 = 1 := by decide +kernel
theorem alpha1_sq_ne_one : alpha1 * alpha1 ≠ 1 := by decide +kernel
theorem beta1_sq : beta1 * beta1 = t := by decide +kernel
theorem beta1_ne_one : beta1 ≠ 1 := by decide +kernel
theorem beta1_pow_four : beta1 ^ 4 = 1 := by decide +kernel
theorem beta1_sq_ne_one : beta1 * beta1 ≠ 1 := by decide +kernel
theorem alpha2_sq : alpha2 * alpha2 = t := by decide +kernel
theorem alpha2_ne_one : alpha2 ≠ 1 := by decide +kernel
theorem alpha2_pow_four : alpha2 ^ 4 = 1 := by decide +kernel
theorem alpha2_sq_ne_one : alpha2 * alpha2 ≠ 1 := by decide +kernel
theorem beta2_sq : beta2 * beta2 = t := by decide +kernel
theorem beta2_ne_one : beta2 ≠ 1 := by decide +kernel
theorem beta2_pow_four : beta2 ^ 4 = 1 := by decide +kernel
theorem beta2_sq_ne_one : beta2 * beta2 ≠ 1 := by decide +kernel
theorem beta_sq : beta * beta = u * t := by decide +kernel
theorem beta_ne_one : beta ≠ 1 := by decide +kernel
theorem beta_pow_four : beta ^ 4 = 1 := by decide +kernel
theorem beta_sq_ne_one : beta * beta ≠ 1 := by decide +kernel
theorem sigma1_conj_u : u * sigma1 * u⁻¹ = sigma2 := by decide +kernel
theorem alpha1_conj_u : u * alpha1 * u⁻¹ = alpha2 := by decide +kernel
theorem beta1_conj_u : u * beta1 * u⁻¹ = beta2 := by decide +kernel
theorem sigma1_mul_u : sigma1 * u = u * sigma2 := by decide +kernel
theorem alpha1_mul_u : alpha1 * u = u * alpha2 := by decide +kernel
theorem beta1_mul_u : beta1 * u = u * beta2 := by decide +kernel
theorem sigma1_conj_v : v * sigma1 * v⁻¹ = sigma1⁻¹ := by decide +kernel
theorem sigma2_conj_v : v * sigma2 * v⁻¹ = sigma2⁻¹ := by decide +kernel
theorem alpha1_conj_v : v * alpha1 * v⁻¹ = alpha1⁻¹ := by decide +kernel
theorem alpha2_conj_v : v * alpha2 * v⁻¹ = alpha2⁻¹ := by decide +kernel
theorem beta1_conj_v : v * beta1 * v⁻¹ = alpha1 * beta1 := by decide +kernel
theorem beta2_conj_v : v * beta2 * v⁻¹ = alpha2 * beta2 := by decide +kernel
theorem u_commute_v : u * v = v * u := by decide +kernel
theorem t_commute_u : t * u = u * t := by decide +kernel
theorem t_commute_v : t * v = v * t := by decide +kernel
theorem t_commute_sigma1 : t * sigma1 = sigma1 * t := by decide +kernel
theorem t_commute_sigma2 : t * sigma2 = sigma2 * t := by decide +kernel
theorem t_commute_alpha1 : t * alpha1 = alpha1 * t := by decide +kernel
theorem t_commute_beta1 : t * beta1 = beta1 * t := by decide +kernel
theorem t_commute_alpha2 : t * alpha2 = alpha2 * t := by decide +kernel
theorem t_commute_beta2 : t * beta2 = beta2 * t := by decide +kernel
theorem sigma1_commute_sigma2 : sigma1 * sigma2 = sigma2 * sigma1 := by decide +kernel
theorem alpha1_commute_alpha2 : alpha1 * alpha2 = alpha2 * alpha1 := by decide +kernel
theorem beta1_commute_beta2 : beta1 * beta2 = beta2 * beta1 := by decide +kernel
theorem alpha1_beta1_alpha1 : alpha1 * beta1 * alpha1 = beta1 := by decide +kernel
theorem alpha1_beta1_eq : alpha1 * beta1 = beta1 * alpha1 * t := by decide +kernel
theorem alpha1_beta1_sq : alpha1 * beta1 * (alpha1 * beta1) = t := by decide +kernel
theorem alpha1_beta1_ne_one : alpha1 * beta1 ≠ 1 := by decide +kernel
theorem alpha2_beta2_alpha2 : alpha2 * beta2 * alpha2 = beta2 := by decide +kernel
theorem alpha2_beta2_eq : alpha2 * beta2 = beta2 * alpha2 * t := by decide +kernel
theorem alpha2_beta2_sq : alpha2 * beta2 * (alpha2 * beta2) = t := by decide +kernel
theorem alpha2_beta2_ne_one : alpha2 * beta2 ≠ 1 := by decide +kernel
theorem beta_mul_u : beta * u = t * beta := by decide +kernel
theorem u_mul_beta : u * beta = beta * t := by decide +kernel
theorem beta_mul_t_mul_beta : beta * t * beta = t := by decide +kernel
theorem beta_mul_u_mul_beta : beta * u * beta = u := by decide +kernel

end CertificateChecks.Parrott946.Alg

end
