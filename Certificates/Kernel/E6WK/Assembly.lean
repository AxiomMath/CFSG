module

public import Certificates.Kernel.E6WK.Checks
public import Certificates.Kernel.E6WK.U0
public import Certificates.Kernel.E6WK.U1
public import CFSG.Certificates.Kernel.E6WKSound

public section

namespace CertificateChecks.KernelE6WK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.KC.E6WK CFSG.KD.E6WK
  CFSG.StandardType.TwE6RootKill

theorem u_checks : ∀ n < up.length, uCheckWith vp rm (up.getD n 0) vk (wit.getD n []) = true := by
  rw [up_wit_length.1]
  intro n hn
  interval_cases n
  exacts [ch830101u0, ch830101u1, ch830101u2, ch830101u3, ch830101u4, ch830101u5, ch830101u6,
    ch830101u7, ch830101u8, ch830101u9, ch830101u10, ch830101u11, ch830101u12, ch830101u13,
    ch830101u14, ch830101u15, ch830101u16, ch830101u17, ch830101u18, ch830101u19, ch830101u20,
    ch830101u21, ch830101u22, ch830101u23, ch830101u24, ch830101u25, ch830101u26]


theorem e6wk_trichotomy (w : WeylGroup TwistTag.E6.tag) :
    (∃ i, IsRoot TwistTag.E6.tag (wkMatrix w i)) ∨ wkMatrix w = 0 ∨
      ∃ R C : Fin 3 → Fin TwistTag.E6.tag.rank,
        ((wkMatrix w).submatrix R C).det ∈ ({1, -1, 2, -2} : Finset ℤ) :=
  trichotomy_of_checks tab_check up_check k_check v_check u_checks w

end CertificateChecks.KernelE6WK
