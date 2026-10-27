module

public import Certificates.Kernel.MonsterExist.ELevel.Check1
public import Certificates.Kernel.MonsterExist.ELevel.Inner1a
public import Certificates.Kernel.MonsterExist.ELevel.Inner1b
public import Certificates.Kernel.MonsterExist.ELevel.Check2
public import Certificates.Kernel.MonsterExist.ELevel.Check6
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 100000

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ELevel

open CFSG.KC CFSG.KC.Loop CFSG.Monster CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Census CertificateChecks.MonsterExist.ShortKey CertificateChecks.MonsterExist.Eb

theorem pass_all {P : ℕ → Bool} (h : ∀ c < 8, passRange P (512 * c) 512 = true) :
    ∀ a < 4096, bucketAll P a = true := by
  intro a ha
  have := (passRange_iff _ _ _).1 (h (a / 512) (by omega)) (a % 512) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

theorem inner_all {TB DB xw nCS CS CV nCV m k : ℕ} {PIV : List (ℕ × ℕ)} (hm : nCV = m * k)
    (h : ∀ c < k, innerRange TB DB PIV xw nCS CS CV (m * c) m = true) :
    ∀ t < nCV, innerV TB DB PIV xw nCS CS (laneW 25 CV t) = true := by
  intro t ht
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      omega
    · exact h0
  have hc : t / m < k := (Nat.div_lt_iff_lt_mul hm0).2 (by rw [Nat.mul_comm]; omega)
  have := (allN_iff _ _).1 (h (t / m) hc) (t % m) (Nat.mod_lt _ hm0)
  have e : Nat.add (m * (t / m)) (t % m) = t := Nat.div_add_mod t m
  rwa [e] at this

theorem check1 : checkX shortPacked (tT 1) (tD 1) (packP (wP 1)) = true :=
  checkX_of_kernel perm1 aut1 basis1 tt1 xw1 sw1 elim1 fb1
    (pass_all fun c hc => by
      interval_cases c
      exacts [pass1_0, pass1_1, pass1_2, pass1_3, pass1_4, pass1_5, pass1_6, pass1_7])
    cv1 cs1
    (inner_all (m := 285) (k := 8) rfl (fun c hc => by
      interval_cases c
      exacts [inner1_0, inner1_1, inner1_2, inner1_3, inner1_4, inner1_5, inner1_6, inner1_7]))

theorem check2 : checkX shortPacked (tT 2) (tD 2) (packP (wP 2)) = true :=
  checkX_of_kernel perm2 aut2 basis2 tt2 xw2 sw2 elim2 fb2
    (pass_all fun c hc => by
      interval_cases c
      exacts [pass2_0, pass2_1, pass2_2, pass2_3, pass2_4, pass2_5, pass2_6, pass2_7])
    cv2 cs2
    (inner_all (m := 66) (k := 4) rfl (fun c hc => by
      interval_cases c
      exacts [inner2_0, inner2_1, inner2_2, inner2_3]))

theorem check6 : checkX shortPacked (tT 6) (tD 6) (packP (wP 6)) = true :=
  checkX_of_kernel (nCV := 0) (nCS := 0) (CV := 0) (CS := 0) perm6 aut6 basis6 tt6 xw6 sw6 elim6 fb6
    (pass_all fun c hc => by
      interval_cases c
      exacts [pass6_0, pass6_1, pass6_2, pass6_3, pass6_4, pass6_5, pass6_6, pass6_7])
    ⟨by norm_num, fun t ht => absurd ht (Nat.not_lt_zero t)⟩ ⟨by norm_num, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    (fun t ht => absurd ht (Nat.not_lt_zero t))

theorem allOK_true : allOK = true := by
  unfold allOK fullOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨rankOKT_of perm1 aut1 basis1 rank1, check1⟩, ⟨rankOKT_of perm2 aut2 basis2 rank2, check2⟩⟩,
    ⟨rankOKT_of perm6 aut6 basis6 rank6, check6⟩⟩

end CertificateChecks.MonsterExist.ELevel

end
