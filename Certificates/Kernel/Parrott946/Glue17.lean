module

public import Certificates.Kernel.Parrott946.Glue
public import Certificates.Kernel.Parrott946.Alg
public import Certificates.Kernel.Parrott946.Checks17
public import Certificates.Data.ParrottPSp43L1

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] noncomputable def wv17 (k : ℕ) : P45 := ((wW.getD k []).map gA').prod

theorem prep_wE {k : ℕ} (hk : k < 49) : PRep 45 6 (wE k) (wv17 k) ∧ wv17 k ∈ A :=
  prep_word c17_words (by rw [c17_orders.2.2.2.2.2.2.2]; exact hk)

theorem wv17_eq {k : ℕ} (hk : k < 10) : wv17 k = elsA.getD k 1 := by
  rw [(elsA_eq (by omega)).1, wv17]
  congr 2
  have h := congrArg (fun l => l.getD k []) c17_els.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk] at h
  simpa only [List.getD_eq_getElem?_getD] using h

theorem prep_el {k : ℕ} (hk : k < 10) : PRep 45 6 (wE k) (elsA.getD k 1) := by
  rw [← wv17_eq hk]
  exact (prep_wE (by omega)).1

theorem prep_t : PRep 45 6 (wE 0) t := prep_el (k := 0) (by norm_num)
theorem prep_u : PRep 45 6 (wE 1) u := prep_el (k := 1) (by norm_num)
theorem prep_v : PRep 45 6 (wE 2) v := prep_el (k := 2) (by norm_num)
theorem prep_sg1 : PRep 45 6 (wE 3) sigma1 := prep_el (k := 3) (by norm_num)
theorem prep_sg2 : PRep 45 6 (wE 4) sigma2 := prep_el (k := 4) (by norm_num)
theorem prep_a1 : PRep 45 6 (wE 5) alpha1 := prep_el (k := 5) (by norm_num)
theorem prep_b1 : PRep 45 6 (wE 6) beta1 := prep_el (k := 6) (by norm_num)
theorem prep_a2 : PRep 45 6 (wE 7) alpha2 := prep_el (k := 7) (by norm_num)
theorem prep_b2 : PRep 45 6 (wE 8) beta2 := prep_el (k := 8) (by norm_num)
theorem prep_beta : PRep 45 6 (wE 9) beta := prep_el (k := 9) (by norm_num)

theorem prep_b5 : PRep 45 6 (wE 10) b5 := by
  rw [Nat.eq_of_beq_eq_true c17_els.2]
  exact prep_cOf _

theorem b5_eq : b5 = wv17 10 := prep_eq prep_b5 (prep_wE (by norm_num)).1

theorem b5_memA : b5 ∈ A := by
  rw [b5_eq]
  exact (prep_wE (by norm_num)).2

theorem prep_pc {P Q : ℕ} {g h : P45} (hP : PRep 45 6 P g) (hQ : PRep 45 6 Q h) :
    PRep 45 6 (pc P Q) (g * h) := prep_pcomp hn45 hP hQ

theorem comm_of_cmm {P Q : ℕ} {g h : P45} (hP : PRep 45 6 P g) (hQ : PRep 45 6 Q h)
    (hc : cmm P Q = true) : g * h = h * g := comm_of_eq22 hP hQ hc

theorem inv_iff_isInvK {P : ℕ} {g : P45} (hP : PRep 45 6 P g) :
    isInvK 45 6 P = true ↔ g * g = 1 ∧ g ≠ 1 := by
  rw [isInvK_iff hn45 hP, orderOf_eq_prime_iff, sq]

end CertificateChecks.Parrott946

end
