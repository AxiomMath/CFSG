module

public import Certificates.Kernel.Sporadic.Fi24G2e.Bridge
public import Certificates.Kernel.Sporadic.Fi24G2e.RData
import Certificates.Kernel.Sporadic.Fi24G2e.RA
import Certificates.Kernel.Sporadic.Fi24G2e.RY
import Certificates.Kernel.Sporadic.Fi24G2e.RZ
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi24G2e

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24Ext CertificateChecks.KernelSpor.Fi24Rels TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KS.Mat3 CFSG.KD.Fi24G2e

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24G2e.BX CFSG.KD.Fi24G2e.RX CFSG.KD.Fi24Ext.MX
  CFSG.KD.BrFi24.MT CFSG.KD.Fi24Fix.MX

theorem dihedral_conj {G : Type*} [Group G] {r y : G} (hr : r * r = 1) (hy : y * y = 1) {k : ℕ}
    (hz : (r * y) ^ (2 * k + 1) = 1) : (r * y) ^ k * r * ((r * y) ^ k)⁻¹ = y := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h1 : r * (r * y)⁻¹ = (r * y) * r := by
    rw [mul_inv_rev, hyi, hri]
    group
  have h2 : ∀ m : ℕ, r * ((r * y) ^ m)⁻¹ = (r * y) ^ m * r := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc r * ((r * y) ^ (m + 1))⁻¹ = (r * (r * y)⁻¹) * ((r * y) ^ m)⁻¹ := by
            rw [pow_succ, mul_inv_rev, mul_assoc]
        _ = (r * y) * (r * ((r * y) ^ m)⁻¹) := by rw [h1, mul_assoc]
        _ = (r * y) ^ (m + 1) * r := by rw [ih, ← mul_assoc, ← pow_succ']
  have h3 : (r * y) ^ (2 * k) = (r * y)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hz]
  calc (r * y) ^ k * r * ((r * y) ^ k)⁻¹ = (r * y) ^ k * ((r * y) ^ k * r) := by
        rw [mul_assoc, h2]
    _ = (r * y) ^ (2 * k) * r := by rw [← mul_assoc, ← pow_add, two_mul]
    _ = y := by rw [h3, mul_inv_rev, hyi, hri, mul_assoc, hr, mul_one]

theorem cn_of_beq {X Y Z : ℕ} (hX : Cn X) (hY : Cn Y) (h : Nat.beq (CFSG.KD.BrFi24.MUL X Y) Z = true) :
    Cn Z := by
  rw [← eq_of_beq h]
  exact (mul_mt hX hY).1

theorem pstep {Z A B C : ℕ} {a b : ℕ} (hA : Cn A ∧ Mt A = Mt Z ^ a) (hB : Cn B ∧ Mt B = Mt Z ^ b)
    (h : Nat.beq (CFSG.KD.BrFi24.MUL A B) C = true) : Cn C ∧ Mt C = Mt Z ^ (a + b) :=
  ⟨cn_of_beq hA.1 hB.1 h, by rw [← mt_mul_eq hA.1 hB.1 h, hA.2, hB.2, pow_add]⟩

theorem pfin {Z A B : ℕ} {a b : ℕ} (n : ℕ) (hn : a + b = n) (hA : Cn A ∧ Mt A = Mt Z ^ a)
    (hB : Cn B ∧ Mt B = Mt Z ^ b)
    (h : Nat.beq (CFSG.KD.BrFi24.MUL A B) CFSG.KD.BrFi24.ONE = true) : Mt Z ^ n = 1 := by
  rw [← hn, pow_add, ← hA.2, ← hB.2]
  exact mt_mul_one hA.1 hB.1 h

theorem cn_H0 : Cn CFSG.KD.Fi24Ext.H0 := cn_MX (k := 45) (by norm_num)

theorem cn_H1 : Cn CFSG.KD.Fi24Ext.H1 := cn_MX (k := 51) (by norm_num)

theorem cn_T : Cn CFSG.KD.Fi24Ext.T := cn_MX (k := 35) (by norm_num)

theorem cn_HS : Cn HS := cn_of_beq cn_H1 cn_H1 CFSG.KD.Fi24G2e.RA.hs

@[expose] noncomputable def hm (z : ℕ) : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  if z = 1 then Mt CFSG.KD.Fi24Ext.H0 else if z = 2 then Mt CFSG.KD.Fi24Ext.H1
    else Mt CFSG.KD.Fi24Ext.H1 * Mt CFSG.KD.Fi24Ext.H1

theorem HR_facts {z : ℕ} (hz : z = 1 ∨ z = 2 ∨ z = 3) : Cn (HR z) ∧ Mt (HR z) = hm z := by
  rcases hz with rfl | rfl | rfl
  · exact ⟨cn_H0, by rw [hm, if_pos rfl]; rfl⟩
  · exact ⟨cn_H1, by rw [hm, if_neg (by norm_num), if_pos rfl]; rfl⟩
  · refine ⟨cn_HS, ?_⟩
    rw [hm, if_neg (by norm_num), if_neg (by norm_num)]
    exact (mt_mul_eq cn_H1 cn_H1 CFSG.KD.Fi24G2e.RA.hs).symm

theorem wordMul_HR {Y : ℕ} (hY : Cn Y) : ∀ w : List ℕ, (∀ z ∈ w, z = 1 ∨ z = 2 ∨ z = 3) →
    Cn (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL HR w Y) ∧
      Mt (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL HR w Y) = (w.map hm).prod * Mt Y
  | [], _ => ⟨hY, by simp [CFSG.KC.Fi24Fix.wordMul]⟩
  | z :: w, hw => by
    obtain ⟨h1, h2⟩ := wordMul_HR hY w (fun z' hz' => hw z' (List.mem_cons_of_mem z hz'))
    have e : CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL HR (z :: w) Y =
        CFSG.KD.BrFi24.MUL (HR z) (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL HR w Y) := rfl
    obtain ⟨hc, hm'⟩ := HR_facts (hw z List.mem_cons_self)
    obtain ⟨h3, h4⟩ := mul_mt hc h1
    rw [e]
    refine ⟨h3, ?_⟩
    rw [h4, h2, hm', List.map_cons, List.prod_cons, Matrix.mul_assoc]

theorem hw_ok : ∀ z ∈ HW0 ++ HW1 ++ WWL ++ WIL, z = 1 ∨ z = 2 ∨ z = 3 := by decide +kernel

theorem cnM_HW {Y : ℕ} (hY : Cn Y) {w : List ℕ} (hsub : ∀ z ∈ w, z ∈ HW0 ++ HW1 ++ WWL ++ WIL) :
    Cn (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL HR w Y) ∧
      Mt (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL HR w Y) = (w.map hm).prod * Mt Y :=
  wordMul_HR hY w fun z hz => hw_ok z (hsub z hz)

theorem D1H_facts : Cn D1H ∧ Mt D1H = (HW1.map hm).prod := by
  have h := cnM_HW cn_one (w := HW1) (fun z hz => by simp [hz])
  rw [eq_of_beq CFSG.KD.Fi24G2e.RA.d1h, mt_one, Matrix.mul_one] at h
  exact h

theorem D1_facts : Cn D1 ∧ Mt D1 = ((HW0 ++ HW1).map hm).prod := by
  have h := cnM_HW D1H_facts.1 (w := HW0) (fun z hz => by simp [hz])
  rw [eq_of_beq CFSG.KD.Fi24G2e.RA.d1, D1H_facts.2, ← List.prod_append, ← List.map_append] at h
  exact h

theorem RD_facts : Cn RD ∧ Mt RD = Mt D1 ^ 7 := by
  have e1 : Cn D1 ∧ Mt D1 = Mt D1 ^ 1 := ⟨D1_facts.1, (pow_one _).symm⟩
  have e2 := pstep e1 e1 CFSG.KD.Fi24G2e.RA.d2
  have e4 := pstep e2 e2 CFSG.KD.Fi24G2e.RA.d4
  have e6 := pstep e4 e2 CFSG.KD.Fi24G2e.RA.d6
  have e7 := pstep e6 e1 CFSG.KD.Fi24G2e.RA.d7
  exact e7

theorem RU2_facts : Cn RU2 ∧ Mt RU2 = Mt RD * (Mt CFSG.KD.Fi24Ext.H0 * (Mt RD * Mt CFSG.KD.Fi24Ext.H0)) := by
  have h1 := mul_mt RD_facts.1 cn_H0
  have h2 := mul_mt cn_H0 h1.1
  have h3 := mul_mt RD_facts.1 h2.1
  rw [eq_of_beq CFSG.KD.Fi24G2e.RA.u2] at h3
  rw [h3.2, h2.2, h1.2]
  exact ⟨h3.1, rfl⟩

theorem WW_facts : Cn WW ∧ Mt WW = (WWL.map hm).prod := by
  have h := cnM_HW cn_one (w := WWL) (fun z hz => by simp [hz])
  rw [eq_of_beq CFSG.KD.Fi24G2e.RA.ww, mt_one, Matrix.mul_one] at h
  exact h

theorem WI_facts : Cn WI ∧ Mt WI = (WIL.map hm).prod := by
  have h := cnM_HW cn_one (w := WIL) (fun z hz => by simp [hz])
  rw [eq_of_beq CFSG.KD.Fi24G2e.RA.wi, mt_one, Matrix.mul_one] at h
  exact h

theorem RU3_facts : Cn RU3 ∧ Mt RU3 = Mt RU2 * (Mt WW * (Mt RD * Mt WI)) := by
  have h1 := mul_mt RD_facts.1 WI_facts.1
  have h2 := mul_mt WW_facts.1 h1.1
  have h3 := mul_mt RU2_facts.1 h2.1
  rw [eq_of_beq CFSG.KD.Fi24G2e.RA.u3] at h3
  rw [h3.2, h2.2, h1.2]
  exact ⟨h3.1, rfl⟩

theorem RDT_facts : Cn RDT ∧ Mt RDT = Mt RD * Mt CFSG.KD.Fi24Ext.T :=
  ⟨cn_of_beq RD_facts.1 cn_T CFSG.KD.Fi24G2e.RA.dt, (mt_mul_eq RD_facts.1 cn_T CFSG.KD.Fi24G2e.RA.dt).symm⟩

theorem RU2T_facts : Cn RU2T ∧ Mt RU2T = Mt RU2 * Mt CFSG.KD.Fi24Ext.T :=
  ⟨cn_of_beq RU2_facts.1 cn_T CFSG.KD.Fi24G2e.RA.u2t,
    (mt_mul_eq RU2_facts.1 cn_T CFSG.KD.Fi24G2e.RA.u2t).symm⟩

theorem RU3T_facts : Cn RU3T ∧ Mt RU3T = Mt RU3 * Mt CFSG.KD.Fi24Ext.T :=
  ⟨cn_of_beq RU3_facts.1 cn_T CFSG.KD.Fi24G2e.RA.u3t,
    (mt_mul_eq RU3_facts.1 cn_T CFSG.KD.Fi24G2e.RA.u3t).symm⟩

theorem rep_mats :
    Mt CFSG.KD.Fi24Ext.H0 * Mt CFSG.KD.Fi24Ext.H0 = 1 ∧
    Mt CFSG.KD.Fi24Ext.H1 * (Mt CFSG.KD.Fi24Ext.H1 * Mt CFSG.KD.Fi24Ext.H1) = 1 ∧
    Mt (REP 0) = (([1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2] : List ℕ).map hm).prod ^ 7 ∧
    Mt (REP 1) = Mt (REP 0) * (Mt CFSG.KD.Fi24Ext.H0 * (Mt (REP 0) * Mt CFSG.KD.Fi24Ext.H0)) ∧
    Mt (REP 2) = Mt (REP 1) * ((([2, 2, 1, 2, 2, 1, 2] : List ℕ).map hm).prod *
      (Mt (REP 0) * (([3, 1, 3, 3, 1, 3, 3] : List ℕ).map hm).prod)) ∧
    REP 3 = CFSG.KD.Fi24Ext.T ∧
    Mt (REP 4) = Mt (REP 0) * Mt CFSG.KD.Fi24Ext.T ∧ Mt (REP 5) = Mt (REP 1) * Mt CFSG.KD.Fi24Ext.T ∧
    Mt (REP 6) = Mt (REP 2) * Mt CFSG.KD.Fi24Ext.T := by
  have hs3 : Mt CFSG.KD.Fi24Ext.H1 * Mt HS = 1 := mt_mul_one cn_H1 cn_HS CFSG.KD.Fi24G2e.RA.h1cb
  rw [← (mt_mul_eq cn_H1 cn_H1 CFSG.KD.Fi24G2e.RA.hs)] at hs3
  refine ⟨mt_mul_one cn_H0 cn_H0 CFSG.KD.Fi24G2e.RA.h0sq, hs3, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · change Mt RD = _
    rw [RD_facts.2, D1_facts.2]
    rfl
  · exact RU2_facts.2
  · change Mt RU3 = Mt RU2 * (_ * (Mt RD * _))
    rw [RU3_facts.2, WW_facts.2, WI_facts.2]
    rfl
  · exact RDT_facts.2
  · exact RU2T_facts.2
  · exact RU3T_facts.2

theorem cn_REP {i : ℕ} (hi : i < 7) : Cn (REP i) := by
  interval_cases i
  · exact RD_facts.1
  · exact RU2_facts.1
  · exact RU3_facts.1
  · exact cn_T
  · exact RDT_facts.1
  · exact RU2T_facts.1
  · exact RU3T_facts.1

theorem rsq_all : ∀ i < 7, Nat.beq (CFSG.KD.BrFi24.MUL (REP i) (REP i)) CFSG.KD.BrFi24.ONE = true :=
  CFSG.KD.Fi24G2e.RA.SQ.all

theorem y_all : ∀ i < 7, Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (GWL i)
    CFSG.KD.BrFi24.ONE) (YY i) = true := CFSG.KD.Fi24G2e.RY.Y.all

theorem z_all : ∀ i < 7, Nat.beq (CFSG.KD.BrFi24.MUL (REP i) (YY i)) (ZZ i) = true :=
  CFSG.KD.Fi24G2e.RY.Z.all

theorem gw_lt : ∀ i < 7, ∀ g ∈ GWL i, g < 12 := by decide +kernel

theorem gw_split : ∀ i < 7, GWL i = GCL i ++ CWL i ++ (GCL i).reverse := by decide +kernel

theorem gc_lt : ∀ i < 7, ∀ g ∈ GCL i, g < 12 := by decide +kernel

theorem YY_facts {i : ℕ} (hi : i < 7) :
    Cn (YY i) ∧ Mt (YY i) = (τ ((GWL i).map g0).prod : Matrix (Fin 781) (Fin 781) (ZMod 3)) := by
  have h := wordMul_τ cn_one (GWL i) (gw_lt i hi)
  rw [eq_of_beq (y_all i hi), mt_one, Matrix.mul_one] at h
  exact h

theorem prod_reverse (w : List ℕ) : (w.reverse.map g0).prod = ((w.map g0).prod)⁻¹ := by
  induction w with
  | nil => simp
  | cons g w ih =>
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [g0_inv]

theorem τ_GWL {i : ℕ} (hi : i < 7) : τ ((GWL i).map g0).prod =
    τ ((GCL i).map g0).prod * τ ((CWL i).map g0).prod * (τ ((GCL i).map g0).prod)⁻¹ := by
  rw [gw_split i hi, List.map_append, List.map_append, List.prod_append, List.prod_append,
    prod_reverse, map_mul, map_mul, map_inv]

theorem τ_CWL_sq {i : ℕ} (hi : i < 7) :
    τ ((CWL i).map g0).prod * τ ((CWL i).map g0).prod = 1 := by
  have key : ∀ (w : List ℕ) (X : ℕ), (∀ g ∈ w, g < 12) →
      Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG w CFSG.KD.BrFi24.ONE) X = true →
      Nat.beq (CFSG.KD.BrFi24.MUL X X) CFSG.KD.BrFi24.ONE = true →
      τ (w.map g0).prod * τ (w.map g0).prod = 1 := by
    intro w X hw h1 h2
    have h := wordMul_τ cn_one w hw
    rw [eq_of_beq h1, mt_one, Matrix.mul_one] at h
    apply Units.ext
    rw [Units.val_mul, ← h.2, Units.val_one]
    exact mt_mul_one h.1 h.1 h2
  have hA := key [0, 2] MWA (by decide) CFSG.KD.Fi24G2e.RA.mwa CFSG.KD.Fi24G2e.RA.mwasq
  have hB := key [0, 2, 4, 6] MWB (by decide) CFSG.KD.Fi24G2e.RA.mwb CFSG.KD.Fi24G2e.RA.mwbsq
  have hD := key [0, 2, 4] MWD (by decide) CFSG.KD.Fi24G2e.RA.mwd CFSG.KD.Fi24G2e.RA.mwdsq
  have hC : τ (([2] : List ℕ).map g0).prod * τ (([2] : List ℕ).map g0).prod = 1 := by
    rw [← map_mul, List.map_singleton, List.prod_singleton, g0_mul_self, map_one]
  interval_cases i
  · exact hA
  · exact hA
  · exact hB
  · exact hC
  · exact hC
  · exact hD
  · exact hD

theorem τ_GWL_sq {i : ℕ} (hi : i < 7) : τ ((GWL i).map g0).prod * τ ((GWL i).map g0).prod = 1 := by
  rw [τ_GWL hi]
  have h := τ_CWL_sq hi
  calc _ = τ ((GCL i).map g0).prod * (τ ((CWL i).map g0).prod * τ ((CWL i).map g0).prod) *
      (τ ((GCL i).map g0).prod)⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem zz_pow {i : ℕ} (hi : i < 7) : Mt (ZZ i) ^ nO i = 1 := by
  have cz : ∀ j < 7, Cn (ZZ j) := fun j hj => cn_of_beq (cn_REP hj) (YY_facts hj).1 (z_all j hj)
  have P := CFSG.KD.Fi24G2e.RZ.P.all
  have F := CFSG.KD.Fi24G2e.RZ.F.all
  interval_cases i
  · have p0 : Cn (ZZ 0) ∧ Mt (ZZ 0) = Mt (ZZ 0) ^ 1 := ⟨cz 0 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 0 (by norm_num))
    have p2 := pstep p1 p1 (P 1 (by norm_num))
    exact pfin _ (by decide) p2 p0 (F 0 (by norm_num))
  · have p0 : Cn (ZZ 1) ∧ Mt (ZZ 1) = Mt (ZZ 1) ^ 1 := ⟨cz 1 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 2 (by norm_num))
    have p2 := pstep p1 p1 (P 3 (by norm_num))
    exact pfin _ (by decide) p2 p0 (F 1 (by norm_num))
  · have p0 : Cn (ZZ 2) ∧ Mt (ZZ 2) = Mt (ZZ 2) ^ 1 := ⟨cz 2 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 4 (by norm_num))
    have p2 := pstep p1 p0 (P 5 (by norm_num))
    have p3 := pstep p2 p2 (P 6 (by norm_num))
    have p4 := pstep p3 p2 (P 7 (by norm_num))
    have p5 := pstep p4 p4 (P 8 (by norm_num))
    exact pfin _ (by decide) p5 p4 (F 2 (by norm_num))
  · have p0 : Cn (ZZ 3) ∧ Mt (ZZ 3) = Mt (ZZ 3) ^ 1 := ⟨cz 3 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 9 (by norm_num))
    exact pfin _ (by decide) p1 p0 (F 3 (by norm_num))
  · have p0 : Cn (ZZ 4) ∧ Mt (ZZ 4) = Mt (ZZ 4) ^ 1 := ⟨cz 4 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 10 (by norm_num))
    exact pfin _ (by decide) p1 p0 (F 4 (by norm_num))
  · have p0 : Cn (ZZ 5) ∧ Mt (ZZ 5) = Mt (ZZ 5) ^ 1 := ⟨cz 5 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 11 (by norm_num))
    have p2 := pstep p1 p1 (P 12 (by norm_num))
    have p3 := pstep p2 p2 (P 13 (by norm_num))
    have p4 := pstep p3 p1 (P 14 (by norm_num))
    exact pfin _ (by decide) p4 p0 (F 5 (by norm_num))
  · have p0 : Cn (ZZ 6) ∧ Mt (ZZ 6) = Mt (ZZ 6) ^ 1 := ⟨cz 6 (by norm_num), (pow_one _).symm⟩
    have p1 := pstep p0 p0 (P 15 (by norm_num))
    have p2 := pstep p1 p0 (P 16 (by norm_num))
    have p3 := pstep p2 p2 (P 17 (by norm_num))
    have p4 := pstep p3 p3 (P 18 (by norm_num))
    have p5 := pstep p4 p4 (P 19 (by norm_num))
    have p6 := pstep p5 p3 (P 20 (by norm_num))
    exact pfin _ (by decide) p6 p2 (F 6 (by norm_num))

theorem nO_odd {i : ℕ} (hi : i < 7) : nO i = 2 * ((nO i - 1) / 2) + 1 := by
  interval_cases i <;> rfl

theorem conj_rep {i : ℕ} (hi : i < 7) (r : GL (Fin 781) (ZMod 3))
    (hr : (r : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (REP i)) :
    (r * τ ((GWL i).map g0).prod) ^ ((nO i - 1) / 2) * r *
      ((r * τ ((GWL i).map g0).prod) ^ ((nO i - 1) / 2))⁻¹ = τ ((GWL i).map g0).prod := by
  have h1 : r * r = 1 := by
    apply Units.ext
    rw [Units.val_mul, hr, Units.val_one]
    exact mt_mul_one (cn_REP hi) (cn_REP hi) (rsq_all i hi)
  have h2 : τ ((GWL i).map g0).prod * τ ((GWL i).map g0).prod = 1 := τ_GWL_sq hi
  have hzv : ((r * τ ((GWL i).map g0).prod : GL (Fin 781) (ZMod 3)) :
      Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (ZZ i) := by
    rw [Units.val_mul, hr, ← (YY_facts hi).2]
    exact mt_mul_eq (cn_REP hi) (YY_facts hi).1 (z_all i hi)
  have h3 : (r * τ ((GWL i).map g0).prod) ^ (2 * ((nO i - 1) / 2) + 1) = 1 := by
    rw [← nO_odd hi]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzv, Units.val_one]
    exact zz_pow hi
  exact @dihedral_conj (GL (Fin 781) (ZMod 3)) Units.instGroup _ _ h1 h2 _ h3

theorem conj_rep_cw {i : ℕ} (hi : i < 7) (r : GL (Fin 781) (ZMod 3))
    (hr : (r : Matrix (Fin 781) (Fin 781) (ZMod 3)) = Mt (REP i)) :
    ((τ ((GCL i).map g0).prod)⁻¹ * (r * τ ((GWL i).map g0).prod) ^ ((nO i - 1) / 2)) * r *
      ((τ ((GCL i).map g0).prod)⁻¹ * (r * τ ((GWL i).map g0).prod) ^ ((nO i - 1) / 2))⁻¹ =
        τ ((CWL i).map g0).prod := by
  have h := conj_rep hi r hr
  have hY := τ_GWL hi
  calc _ = (τ ((GCL i).map g0).prod)⁻¹ * (((r * τ ((GWL i).map g0).prod) ^ ((nO i - 1) / 2)) * r *
        ((r * τ ((GWL i).map g0).prod) ^ ((nO i - 1) / 2))⁻¹) * τ ((GCL i).map g0).prod := by group
    _ = (τ ((GCL i).map g0).prod)⁻¹ * (τ ((GCL i).map g0).prod * τ ((CWL i).map g0).prod *
        (τ ((GCL i).map g0).prod)⁻¹) * τ ((GCL i).map g0).prod := by rw [h, hY]
    _ = τ ((CWL i).map g0).prod := by group

end CertificateChecks.KernelFi24G2e

end
