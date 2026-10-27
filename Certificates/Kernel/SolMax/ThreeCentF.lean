module

public import Certificates.Kernel.SolMax.ThreeCent
public import CFSG.Certificates.Kernel.SolMaxSound

public section

namespace CertificateChecks.KernelSolMax.ThreeCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.SolMax.SixGen CFSG.ComponentClassification.SolMax.ThreeCent
open CFSG.KC.SolMax

theorem parts {c : Swaps × List Swaps × Nat} {k cnt U : Nat} {G T PL : Nat → Nat}
    (h1 : bAnd(gensK (gsOf c) 9 4 k G, bAnd(Nat.beq cnt c.2.2,
      penumHdK (pidn 9 4) cnt c.2.2 T PL)) = true)
    (h2 : bAnd(bindArrK (tabOf (permOf c.1)) 9 4 U, bAnd(canonK 9 4 (mask 4) (9 * 4) U,
      bAnd(commK k G U, bAnd(restXK cnt T, restYK cnt T)))) = true) :
    GensOK 9 4 k G (gsOf c) ∧ cnt = c.2.2 ∧ penumHdK (pidn 9 4) cnt c.2.2 T PL = true ∧
      tabOf (permOf c.1) = unpack 9 4 U ∧ Cn U ∧ commK k G U = true ∧ restXK cnt T = true ∧
      restYK cnt T = true := by
  obtain ⟨a1, a2, a3⟩ := (by simpa only [bAnd_iff] using h1 :
    gensK (gsOf c) 9 4 k G = true ∧ Nat.beq cnt c.2.2 = true ∧ _)
  obtain ⟨b1, b2, b3, b4, b5⟩ := (by simpa only [bAnd_iff] using h2 :
    bindArrK (tabOf (permOf c.1)) 9 4 U = true ∧ _ ∧ _ ∧ _ ∧ _)
  exact ⟨gensOK_of a1, Nat.eq_of_beq_eq_true a2, a3, unpack_eq_of_bindArrK b1, b2, b3, b4, b5⟩

theorem case0 : threeCentCaseOK (threeCentCases.getD 0 default) = true := by
  obtain ⟨hg, hc, hh, hu, hU, hm, hx, hy⟩ := parts (c := threeCentCases.getD 0 default)
    (k := TC0.k) (cnt := TC0.cnt) (U := UP 0) (G := TC0.G) (T := TC0.T) (PL := TC0.PL) k0_hd k0_x
  have e : TC0.cnt = 2160 := rfl
  exact threeCase_of hg hh (fun i hi => penumSl_spec k0_sl i (Nat.zero_le _)
    (by omega) hi) hc hu hU hm hx hy

theorem case1 : threeCentCaseOK (threeCentCases.getD 1 default) = true := by
  obtain ⟨hg, hc, hh, hu, hU, hm, hx, hy⟩ := parts (c := threeCentCases.getD 1 default)
    (k := TC1.k) (cnt := TC1.cnt) (U := UP 1) (G := TC1.G) (T := TC1.T) (PL := TC1.PL) k1_hd k1_x
  have e : TC1.cnt = 108 := rfl
  exact threeCase_of hg hh (fun i hi => penumSl_spec k1_sl i (Nat.zero_le _)
    (by omega) hi) hc hu hU hm hx hy

theorem case2 : threeCentCaseOK (threeCentCases.getD 2 default) = true := by
  obtain ⟨hg, hc, hh, hu, hU, hm, hx, hy⟩ := parts (c := threeCentCases.getD 2 default)
    (k := TC2.k) (cnt := TC2.cnt) (U := UP 2) (G := TC2.G) (T := TC2.T) (PL := TC2.PL) k2_hd k2_x
  have e : TC2.cnt = 162 := rfl
  exact threeCase_of hg hh (fun i hi => penumSl_spec k2_sl i (Nat.zero_le _)
    (by omega) hi) hc hu hU hm hx hy

theorem threeCent_true : threeCentCheck = true := by
  have e : threeCentCases = [threeCentCases.getD 0 default, threeCentCases.getD 1 default,
      threeCentCases.getD 2 default] := rfl
  unfold threeCentCheck
  rw [e]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨case0, case1, case2⟩

end CertificateChecks.KernelSolMax.ThreeCent

end
