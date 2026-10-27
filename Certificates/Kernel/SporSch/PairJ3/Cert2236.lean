
module

public import Certificates.Kernel.SporSch.PairJ3.Check2236
public import Certificates.Kernel.SporSch.PairJ3.FormsLe
public import CFSG.Certificates.Kernel.SporSch.HexLe70Sound

public section

namespace CertificateChecks.KernelSporSch.PJ3Cert

open CFSG.KS.SporSch CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem le70Str_hexAt_lt {s : String} (h : Le70Str s) (o d : Nat) :
    hexAt s.toUTF8 o d < 2 ^ (4 * d) := by
  obtain ⟨cs, rfl, hc⟩ := h
  exact hexAt_lt_le70 hc o d

theorem invWord_lt : decide (j3InvWord < 2 ^ 3240) = true := by
  have h := le70Str_hexAt_lt PJ3F.j3InvHex.ok 0 810
  rewrite [(by norm_num : 4 * 810 = 3240)] at h
  rewrite [j3InvWord]
  exact decide_eq_true h

theorem formWords_lt (h : Le70Str j3FormsHex) :
    allLt 6156 (fun r => decide (hexAt j3FormsHex.toUTF8 (810 * r) 810 < 2 ^ 3240)) = true := by
  rewrite [allLt_iff]
  intro r _
  have h' := le70Str_hexAt_lt h (810 * r) 810
  rewrite [(by norm_num : 4 * 810 = 3240)] at h'
  exact decide_eq_true h'

theorem certOK_of_le70 (h : Le70Str j3FormsHex) : j3CertOK = true := by
  obtain ⟨h7, h8, h9, h10, h11, h12⟩ := stab_checks PJ3Cert.stab
  unfold j3CertOK
  exact with_of _ _ PJ3St.R stab_eq monomials_checks.1 monomials_checks.2 (formWords_lt h)
    invWord_lt (by simp [j3StrongArrs]) gens_ok h7 h8 h9 h10 h11 h12

open PJ3FT in
theorem forms_le70 : Le70Str j3FormsHex := by
  refine ⟨PJ3FT.chars, PJ3FT.eq, ?_⟩
  delta PJ3FT.chars
  simp only [le70K_append, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12,
    ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28,
    ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, Bool.and_self]

theorem certOK : j3CertOK = true := certOK_of_le70 forms_le70

end CertificateChecks.KernelSporSch.PJ3Cert

end
