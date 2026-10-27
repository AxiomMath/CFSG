module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartInputs
public import Certificates.Data.Kernel.F48Small.Sp43c
public import Certificates.Kernel.Misc.StrsCodes
meta import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartInputs
public import Mathlib
meta import Mathlib

public section

#ks_strs_codes CertificateChecks.KernelF48S.Sp43cB CFSG.ASVolI.burnsideF48s_sp43c_Bw
  CFSG.KC.F48S.decSp43c "abcpqABCPQ"

#ks_strs_codes CertificateChecks.KernelF48S.Sp43cS CFSG.ASVolI.burnsideF48s_sp43c_Sw
  CFSG.KC.F48S.decSp43c "abcpqABCPQ"

#ks_strs_codes CertificateChecks.KernelF48S.Sp43cP1 CFSG.ASVolI.burnsideF48s_sp43c_P1w
  CFSG.KC.F48S.decSp43c "abcpqABCPQ"

#ks_strs_codes CertificateChecks.KernelF48S.Sp43cP2 CFSG.ASVolI.burnsideF48s_sp43c_P2w
  CFSG.KC.F48S.decSp43c "abcpqABCPQ"

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L CFSG.KC.Ord CFSG.Quasithin

@[expose] noncomputable def wB43c : List (List (Fin 2 × Bool)) := Sp43cB.codes.map (List.map letB43c)

@[expose] noncomputable def wS43c : List (List (Fin 2 × Bool)) := Sp43cS.codes.map (List.map letS43c)

@[expose] noncomputable def wP143c : List (List (Fin 3 × Bool)) :=
  Sp43cP1.codes.map (List.map letP43c)

@[expose] noncomputable def wP243c : List (List (Fin 3 × Bool)) :=
  Sp43cP2.codes.map (List.map letQ43c)

@[expose] noncomputable def sLS43c : List (List ℕ) :=
  [burnsideF48s_sp43c_L 1, compL (burnsideF48s_sp43c_L 0) (burnsideF48s_sp43c_L 0)]

@[expose] noncomputable def sLSi43c : List (List ℕ) :=
  [burnsideF48s_sp43c_Li 1, compL (burnsideF48s_sp43c_Li 0) (burnsideF48s_sp43c_Li 0)]

@[expose] noncomputable def qLS43c : List (List ℕ) :=
  [burnsideF48s_sp43c_L 0, burnsideF48s_sp43c_L 1, burnsideF48s_sp43c_L 3]

@[expose] noncomputable def qLSi43c : List (List ℕ) :=
  [burnsideF48s_sp43c_Li 0, burnsideF48s_sp43c_Li 1, burnsideF48s_sp43c_Li 3]

@[expose] noncomputable def bK43c (i : ℕ) : ℕ :=
  evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL) (wB43c.getD i [])

@[expose] noncomputable def dK43c (j : ℕ) : ℕ :=
  evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL)
    (burnsideF48s_sp43c_Dw.getD j [])

@[expose] noncomputable def coverK43c (s : ℕ) (tr : List ℕ) (wit : List (ℕ × ℕ))
    (dec : List (List (ℕ × ℕ × ℕ))) : Bool :=
  ((List.range 162).all fun i =>
    decide ((wit.getD i (0, 0)).1 < 3) &&
      Nat.beq (pcomp (bK43c i) 45 (encL (burnsideF48s_sp43c_L s)))
        (pcomp (pcomp (bK43c (tr.getD (wit.getD i (0, 0)).1 0)) 45 (encL (burnsideF48s_sp43c_L s)))
          45 (bK43c (wit.getD i (0, 0)).2))) &&
  ((List.range 8).all fun j => (List.range 3).all fun t =>
    decide (((dec.getD j []).getD t (0, 0, 0)).1 < 8) &&
      Nat.beq (pcomp (pcomp (dK43c j) 45 (bK43c (tr.getD t 0))) 45 (encL (burnsideF48s_sp43c_L s)))
        (pcomp (pcomp (bK43c ((dec.getD j []).getD t (0, 0, 0)).2.1) 45
          (dK43c ((dec.getD j []).getD t (0, 0, 0)).1)) 45
          (bK43c ((dec.getD j []).getD t (0, 0, 0)).2.2)))

@[expose] noncomputable def sT43c : NT :=
  setT (wS43c.map (evK 45 (sLS43c.map encL) (sLSi43c.map encL)))

@[expose] noncomputable def checkSK43c (T : NT) : Bool :=
  (wS43c.all fun w =>
    memT T (pcomp (pcomp (encL (burnsideF48s_sp43c_L 0)) 45
      (evK 45 (sLS43c.map encL) (sLSi43c.map encL) w)) 45 (encL (burnsideF48s_sp43c_Li 0))) &&
    (memT T (pcomp (pcomp (encL (burnsideF48s_sp43c_Li 0)) 45
      (evK 45 (sLS43c.map encL) (sLSi43c.map encL) w)) 45 (encL (burnsideF48s_sp43c_L 0))) &&
    (memT T (pcomp (pcomp (encL (burnsideF48s_sp43c_L 1)) 45
      (evK 45 (sLS43c.map encL) (sLSi43c.map encL) w)) 45 (encL (burnsideF48s_sp43c_Li 1))) &&
    memT T (pcomp (pcomp (encL (burnsideF48s_sp43c_Li 1)) 45
      (evK 45 (sLS43c.map encL) (sLSi43c.map encL) w)) 45 (encL (burnsideF48s_sp43c_L 1)))))) &&
  !(memT T (pcomp (pcomp (encL (burnsideF48s_sp43c_L 2)) 45 (encL (burnsideF48s_sp43c_L 1))) 45
      (encL (burnsideF48s_sp43c_Li 2)))) &&
  !(memT T (pcomp (pcomp (encL (burnsideF48s_sp43c_L 3)) 45
      (pcomp (encL (burnsideF48s_sp43c_L 0)) 45 (encL (burnsideF48s_sp43c_L 0)))) 45
      (encL (burnsideF48s_sp43c_Li 3))))

theorem codes43c_ok : codesLt10 Sp43cB.codes = true ∧ codesLt10 Sp43cS.codes = true ∧
    codesLt10 Sp43cP1.codes = true ∧ codesLt10 Sp43cP2.codes = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem gens43c_ok : burnsideF48s_sp43c_checkGens () = true := by decide +kernel

theorem far43c_ok : burnsideF48s_sp43c_checkFar () = true := by decide +kernel

theorem xy43c_ok : burnsideF48s_sp43c_checkXY () = true := by decide +kernel

theorem shape43c_ok : (wB43c.length = 162 ∧ [] ∈ wB43c) ∧ (wS43c.length = 81 ∧ [] ∈ wS43c) ∧
    (wP143c.length = 648 ∧ [] ∈ wP143c) ∧ (wP243c.length = 648 ∧ [] ∈ wP243c) := by
  decide +kernel

theorem subB43c_ok : groupK 45
    (wB43c.map (evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL)))
    ([0, 1].map (getK (burnsideF48s_sp43c_LS.map encL))) = true := by decide +kernel

theorem subS43c_ok : groupK 45 (wS43c.map (evK 45 (sLS43c.map encL) (sLSi43c.map encL)))
    ([0, 1].map (getK (sLS43c.map encL))) = true := by decide +kernel

theorem subP143c_ok : groupK 45
    (wP143c.map (evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL)))
    ([0, 1, 2].map (getK (burnsideF48s_sp43c_LS.map encL))) = true := by decide +kernel

theorem subP243c_ok : groupK 45 (wP243c.map (evK 45 (qLS43c.map encL) (qLSi43c.map encL)))
    ([0, 1, 2].map (getK (qLS43c.map encL))) = true := by decide +kernel

theorem cover43c_ok : coverK43c 2 burnsideF48s_sp43c_trP burnsideF48s_sp43c_witP
      burnsideF48s_sp43c_decP = true ∧
    coverK43c 3 burnsideF48s_sp43c_trQ burnsideF48s_sp43c_witQ burnsideF48s_sp43c_decQ = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem s43c_ok : checkSK43c sT43c = true := by decide +kernel

theorem not43c_ok :
    (!memT (setT (wP243c.map (evK 45 (qLS43c.map encL) (qLSi43c.map encL))))
      (encL (burnsideF48s_sp43c_L 2)) &&
    !memT (setT (wP143c.map
      (evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL))))
      (encL (burnsideF48s_sp43c_L 3))) = true := by
  decide +kernel

theorem neg_subP143c : notB (groupK 45
    (wP143c.map (evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL))).tail
    ([0, 1, 2].map (getK (burnsideF48s_sp43c_LS.map encL)))) = true := by decide +kernel

theorem neg_nodup43c : notB (nodupT
    ((wB43c.map (evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL))).take 5
      ++ [evK 45 (burnsideF48s_sp43c_LS.map encL) (burnsideF48s_sp43c_LSi.map encL) ([] : List (Fin 2 × Bool))])
    NT.lf) = true := by decide +kernel

theorem neg_cover43c : notB (coverK43c 2 burnsideF48s_sp43c_trQ burnsideF48s_sp43c_witP
    burnsideF48s_sp43c_decP) = true := by decide +kernel

theorem neg_s43c : notB (checkSK43c
    (setT (wS43c.map (evK 45 (sLS43c.map encL) (sLSi43c.map encL))).tail)) = true := by
  decide +kernel

end CertificateChecks.KernelF48S
