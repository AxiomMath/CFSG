module

public import Certificates.Kernel.SolMax.EightPerm
public import CFSG.Certificates.Kernel.SolMaxSound

public section

namespace CertificateChecks.KernelSolMax.EightPerm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.SolMax.SixGen CFSG.ComponentClassification.SolMax.EightPerm
open CFSG.KC.SolMax

theorem parts {c : Swaps × List Swaps × Nat} {k cnt U : Nat} {G T PL : Nat → Nat}
    (h1 : bAnd(gensK (gsOf c) 9 4 k G, bAnd(Nat.beq cnt c.2.2,
      penumHdK (pidn 9 4) cnt c.2.2 T PL)) = true)
    (h2 : bAnd(bindArrK (tabOf (permOf c.1)) 9 4 U, bAnd(canonK 9 4 (mask 4) (9 * 4) U,
      bAnd(commK k G U, restZK U cnt T))) = true) :
    GensOK 9 4 k G (gsOf c) ∧ cnt = c.2.2 ∧ penumHdK (pidn 9 4) cnt c.2.2 T PL = true ∧
      tabOf (permOf c.1) = unpack 9 4 U ∧ Cn U ∧ commK k G U = true ∧ restZK U cnt T = true := by
  obtain ⟨a1, a2, a3⟩ := (by simpa only [bAnd_iff] using h1 :
    gensK (gsOf c) 9 4 k G = true ∧ Nat.beq cnt c.2.2 = true ∧ _)
  obtain ⟨b1, b2, b3, b4⟩ := (by simpa only [bAnd_iff] using h2 :
    bindArrK (tabOf (permOf c.1)) 9 4 U = true ∧ _ ∧ _ ∧ _)
  exact ⟨gensOK_of a1, Nat.eq_of_beq_eq_true a2, a3, unpack_eq_of_bindArrK b1, b2, b3, b4⟩

theorem case0 : eightPermCaseOK (eightPermCases.getD 0 default) = true := by
  obtain ⟨hg, hc, hh, hu, hU, hm, hz⟩ := parts (c := eightPermCases.getD 0 default)
    (k := EP0.k) (cnt := EP0.cnt) (U := UP 0) (G := EP0.G) (T := EP0.T) (PL := EP0.PL) k0_hd k0_x
  have e : EP0.cnt = 288 := rfl
  exact eightCase_of hg hh (fun i hi => penumSl_spec k0_sl i (Nat.zero_le _)
    (by omega) hi) hc hu hU hm hz

theorem case1 : eightPermCaseOK (eightPermCases.getD 1 default) = true := by
  obtain ⟨hg, hc, hh, hu, hU, hm, hz⟩ := parts (c := eightPermCases.getD 1 default)
    (k := EP1.k) (cnt := EP1.cnt) (U := UP 1) (G := EP1.G) (T := EP1.T) (PL := EP1.PL) k1_hd k1_x
  have e : EP1.cnt = 384 := rfl
  exact eightCase_of hg hh (fun i hi => penumSl_spec k1_sl i (Nat.zero_le _)
    (by omega) hi) hc hu hU hm hz

theorem eightPerm_true : eightPermCheck = true := by
  have e : eightPermCases = [eightPermCases.getD 0 default, eightPermCases.getD 1 default] := rfl
  unfold eightPermCheck
  rw [e]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨case0, case1⟩

end CertificateChecks.KernelSolMax.EightPerm

end
