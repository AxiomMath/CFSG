module

public import Certificates.Kernel.Sporadic.Fi24F4.WGlue
public import Certificates.Kernel.Sporadic.Fi24F4.WCov0
public import Certificates.Kernel.Sporadic.Fi24F4.WCov1
public import Certificates.Kernel.Sporadic.Fi24F4.WCov2
public import Certificates.Kernel.Sporadic.Fi24F4.WCov3
public import Certificates.Kernel.Sporadic.Fi24F4.WCov4
public import Certificates.Kernel.Sporadic.Fi24F4.WPt
public import Certificates.Kernel.Sporadic.Fi24R2W.Group

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Fi24F4W CFSG.KS.Fi24F4W CFSG.KS.Fi24Kit
open CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO.Group
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 M)
open CFSG.Sporadic.FischerOddCore (rep7 m23 fi24R2 fi23U2 fi23U3)
open CFSG.EvenSporadicStandard.YS14 CertificateChecks.KernelSpor.Fi24R2W
open CFSG.KC.Fi24R2W (SD SU2 SR)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem m23_eq (u : CFSG.Sporadic.Fi23.J) : m23 u = jR (phi u) := rfl

theorem m23_mul_self {u : CFSG.Sporadic.Fi23.J} (hu : u * u = 1) : m23 u * m23 u = 1 := by
  rw [m23_eq, ← map_mul, ← map_mul, hu, map_one, map_one]

theorem m23_comm_tR (u : CFSG.Sporadic.Fi23.J) : m23 u * tR = tR * m23 u :=
  CFSG.Sporadic.Fi24.jR_comm_tR (CFSG.Sporadic.Fi24.fi23EquivM.symm u).2

theorem mul_tR_mul_self {u : CFSG.Sporadic.Fi23.J} (hu : u * u = 1) :
    m23 u * tR * (m23 u * tR) = 1 := by
  calc m23 u * tR * (m23 u * tR) = m23 u * (tR * m23 u) * tR := by group
    _ = m23 u * (m23 u * tR) * tR := by rw [m23_comm_tR]
    _ = (m23 u * m23 u) * (tR * tR) := by group
    _ = 1 := by rw [m23_mul_self hu, CFSG.Sporadic.Fi24.tR_mul_tR, one_mul]

theorem m23_val {u : CFSG.Sporadic.Fi23.J} {cs : List ℕ} (hcs : ∀ l ∈ cs, l < 26)
    (hu : phi u = prodC cs) (x : Fin 306936) : (m23 u • x).val = wN NW cs x.val := by
  rw [m23_eq, CFSG.Sporadic.Fi24.jR_smul, hu, ← (idx_prodC cs hcs x.val x.isLt).1,
    CFSG.Sporadic.Th.idx_of_lt _ x.isLt]

theorem m23T_val {u : CFSG.Sporadic.Fi23.J} {cs : List ℕ} (hcs : ∀ l ∈ cs, l < 26)
    (hu : phi u = prodC cs) (x : Fin 306936) :
    ((m23 u * tR) • x).val = wN NW cs (CFSG.KS.Fi24Net.pF NT x.val) := by
  rw [mul_smul, m23_val hcs hu, tR_val CertificateChecks.KernelFi24OrbL.bridge]

theorem phi_u3 : phi fi23U3 = prodC SR := by
  rw [← fi24R2_eq]
  rfl

theorem d_mul_self : CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d = 1 := CFSG.Sporadic.Fi23.d_sq

theorem u2_mul_self : fi23U2 * fi23U2 = 1 := by
  rw [← sq]
  exact (CFSG.Sporadic.FischerOddCore.fi23U2_facts).1

theorem u3_mul_self : fi23U3 * fi23U3 = 1 := by
  rw [← sq]
  exact (CFSG.Sporadic.FischerOddCore.fi23U3_facts).1

theorem data_ok : ∀ i < 5, (∀ l ∈ nthL W.cs i, l < 26) ∧
    (∀ c ∈ W.prods.getD i [], ∀ l ∈ c, l < 26) ∧ (∀ q ∈ nthL W.Q i, q < 306936) ∧
    (∀ q ∈ nthL W.Qc i, q < 306936) ∧
    (∀ e ∈ W.E.getD i [], nthN e 0 < 306936 ∧ nthN e 1 < 306936 ∧ nthN e 2 < 306936) ∧
    (∀ e ∈ W.E.getD i [], nthN e 1 ∈ nthL W.Q i) ∧ (∀ q ∈ nthL W.Qc i, q ∈ nthL W.Q i) ∧
    nthN (nthL W.Q i) 0 = nthN W.q0 i ∧ 0 < (nthL W.Q i).length ∧
    nthN W.xd i < 306936 ∧ nthN W.x1 i < 306936 := by
  decide +kernel

theorem cs_eq : nthL W.cs 0 = SD ∧ nthL W.cs 1 = SU2 ∧ nthL W.cs 2 = SR ∧ nthL W.cs 3 = SU2 ∧
    nthL W.cs 4 = SR := by decide +kernel

theorem tB_eq : tB 0 = false ∧ tB 1 = false ∧ tB 2 = false ∧ tB 3 = true ∧ tB 4 = true := by
  decide +kernel

theorem witFacts_i {i : ℕ} (hi : i < 5) {r : R}
    (hr : ∀ x : Fin 306936, (r • x).val = rG NW NT (nthL W.cs i) (tB i) x.val) (hrr : r * r = 1)
    (hcov : cov i = true) (hprd : prd i = true) (hwit : wit i = true) (hgph : gph i = true)
    (hfixq : fixq i = true) (hnd : nd i = true) : WitFacts r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := data_ok i hi
  exact witFacts_of CertificateChecks.KernelFi24OrbL.bridge hr hrr h1 h2 h3 h4 h5 h6 h7 h8 h9
    ⟨h10, h11⟩ hcov hprd hwit hgph hfixq hnd

theorem rG_false (cs : List ℕ) (x : ℕ) : rG NW NT cs false x = wN NW cs x := rfl

theorem rG_true (cs : List ℕ) (x : ℕ) : rG NW NT cs true x = wN NW cs (CFSG.KS.Fi24Net.pF NT x) :=
  rfl

theorem witFacts_rep7 : WitFacts (rep7 0) ∧ WitFacts (rep7 1) ∧ WitFacts (rep7 2) ∧
    WitFacts (rep7 5) ∧ WitFacts (rep7 6) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := cs_eq
  obtain ⟨t0, t1, t2, t3, t4⟩ := tB_eq
  have hSD : ∀ l ∈ SD, l < 26 := by decide
  have hSU2 : ∀ l ∈ SU2, l < 26 := by decide
  have hSR : ∀ l ∈ SR, l < 26 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine witFacts_i (i := 0) (by norm_num) (fun x => ?_) (m23_mul_self d_mul_self)
      Ck.cov0 Ck.prd0 Ck.wit0 Ck.gph0 Ck.fixq0 Ck.nd0
    change (m23 CFSG.Sporadic.Fi23.d • x).val = _
    rw [c0, t0, rG_false, m23_val hSD phi_d]
  · refine witFacts_i (i := 1) (by norm_num) (fun x => ?_) (m23_mul_self u2_mul_self)
      Ck.cov1 Ck.prd1 Ck.wit1 Ck.gph1 Ck.fixq1 Ck.nd1
    change (m23 fi23U2 • x).val = _
    rw [c1, t1, rG_false, m23_val hSU2 phi_u2]
  · refine witFacts_i (i := 2) (by norm_num) (fun x => ?_) (m23_mul_self u3_mul_self)
      Ck.cov2 Ck.prd2 Ck.wit2 Ck.gph2 Ck.fixq2 Ck.nd2
    change (m23 fi23U3 • x).val = _
    rw [c2, t2, rG_false, m23_val hSR phi_u3]
  · refine witFacts_i (i := 3) (by norm_num) (fun x => ?_) (mul_tR_mul_self u2_mul_self)
      Ck.cov3 Ck.prd3 Ck.wit3 Ck.gph3 Ck.fixq3 Ck.nd3
    change ((m23 fi23U2 * tR) • x).val = _
    rw [c3, t3, rG_true, m23T_val hSU2 phi_u2]
  · refine witFacts_i (i := 4) (by norm_num) (fun x => ?_) (mul_tR_mul_self u3_mul_self)
      Ck.cov4 Ck.prd4 Ck.wit4 Ck.gph4 Ck.fixq4 Ck.nd4
    change ((m23 fi23U3 * tR) • x).val = _
    rw [c4, t4, rG_true, m23T_val hSR phi_u3]

end CFSG.KD.Fi24F4

end
