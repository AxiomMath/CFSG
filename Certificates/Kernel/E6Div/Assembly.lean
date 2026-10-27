module

public import Certificates.Kernel.E6WK.Checks
public import Certificates.Kernel.E6Div.Checks
public import Certificates.Kernel.E6Div.U0
public import Certificates.Kernel.E6Div.U1
public import CFSG.Certificates.Kernel.E6DivSound

public section

namespace CertificateChecks.KernelE6Div

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.KC.E6WK CFSG.KC.E6Div
  Certificates.E6WeylMinors
open CFSG.KD.E6WK (vp up vk)
open CFSG.KD.E6Div (wit)

theorem u_checks : ∀ n < up.length, uCheckDiv vp (up.getD n 0) vk (wit.getD n []) = true := by
  rw [KernelE6WK.up_wit_length.1]
  intro n hn
  interval_cases n
  exacts [ch715001u0, ch715001u1, ch715001u2, ch715001u3, ch715001u4, ch715001u5, ch715001u6,
    ch715001u7, ch715001u8, ch715001u9, ch715001u10, ch715001u11, ch715001u12, ch715001u13,
    ch715001u14, ch715001u15, ch715001u16, ch715001u17, ch715001u18, ch715001u19, ch715001u20,
    ch715001u21, ch715001u22, ch715001u23, ch715001u24, ch715001u25, ch715001u26]


theorem e6div_holds (w : WeylGroup Tag.E6) :
    (weylMatrix w * weylMatrix w = 1 ∨
        SmallMinor 3 (weylMatrix w + 1) ∧ SmallMinor 2 (weylMatrix w - 1)) ∧
    (weylMatrix w * rhoMatrix * (weylMatrix w * rhoMatrix) = 1 ∨
        SmallMinor 3 (weylMatrix w * rhoMatrix - 1) ∧ SmallMinor 2 (weylMatrix w * rhoMatrix + 1)) :=
  e6div_of_checks KernelE6WK.tab_check KernelE6WK.up_check KernelE6WK.k_check KernelE6WK.v_check
    u_checks w0_check w

end CertificateChecks.KernelE6Div
