module

public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.Sporadic.HNSchreier.LevelInputs
public import Certificates.Kernel.HNChain.Regs
public import Certificates.Kernel.HNChain.Tree
import Certificates.Kernel.HNChain.Checks.K
import Certificates.Kernel.HNChain.Checks.L1
import Certificates.Kernel.HNChain.Checks.L2
import Certificates.Kernel.HNChain.Checks.R
import Certificates.Kernel.HNChain.Checks.X
import Certificates.Kernel.HNLocal.Checks.K
import Certificates.Kernel.HNLocal.Fix
import Certificates.Kernel.SporSch.HN.OrbCert
import Certificates.Certificate2102
public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
public import Certificates.Data.Kernel.SporSch.HNXBind
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.SporSch.HNXCnt.Asm
import CFSG.Certificates.Kernel.SporSch.HNXCnt.Native
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.SporSch.HNXCertSound
public import Certificates.Data.Kernel.SporSch.HNXPrim

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNChain

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNLocal CFSG.KD.HNChain CFSG.Sporadic.F5
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open scoped Matrix

local notation "OM" => CFSG.KS.HNLocal.OM
local notation "cv" => CFSG.KS.HNLocal.cvec
local notation "MM" => CFSG.KD.HNLocal.M

theorem PK_xv {i : ℕ} (hi : i < 1140000) :
    PK i = cv (CFSG.KS.SporSch.HNXP.xv CFSG.KD.LgHNX.TX i) := by
  obtain ⟨hd, hlen, -, -, -, -, -, -, hval⟩ :=
    CFSG.KS.SporSch.HNXP.bind_facts CertificateChecks.KernelSporSch.HNXCert.hns_bind
  unfold PK
  rw [CertificateChecks.KernelSporSch.HNXCert.hns_orbit,
    CFSG.KS.SporSch.HNXP.toOrbit_keys_get _ (by rw [hlen]; exact hi), hd, (hval i hi).1,
    CFSG.KS.SporSch.HNXP.toVecB_orbitVector]
  rfl

theorem chainPt_val : (chainPt 0).val = 0 ∧ (chainPt 1).val = 543953 ∧
    (chainPt 2).val = 147358 ∧ (chainPt 3).val = 549971 := by
  decide +kernel

theorem PK_V {i v : ℕ} (hi : i < 1140000) (h : CFSG.KS.SporSch.vecAt CFSG.KD.LgHNX.TX i v = true) :
    PK i = cv v := by
  rw [PK_xv hi]
  exact congrArg _ (Nat.eq_of_beq_eq_true h).symm

theorem PK_c0 : PK (chainPt 0).val = cv V0 := by rw [chainPt_val.1]; exact PK_V (by norm_num) tx0
theorem PK_c1 : PK (chainPt 1).val = cv V1 := by rw [chainPt_val.2.1]; exact PK_V (by norm_num) tx1
theorem PK_c2 : PK (chainPt 2).val = cv V2 := by
  rw [chainPt_val.2.2.1]; exact PK_V (by norm_num) tx2
theorem PK_c3 : PK (chainPt 3).val = cv V3 := by
  rw [chainPt_val.2.2.2]; exact PK_V (by norm_num) tx3

theorem V_canon : CFSG.KS.HNLocal.CCanon V0 ∧ CFSG.KS.HNLocal.CCanon V1 ∧
    CFSG.KS.HNLocal.CCanon V2 ∧ CFSG.KS.HNLocal.CCanon V3 := by
  unfold CFSG.KS.HNLocal.CCanon
  decide +kernel

theorem canon_RB {r : ℕ} (h0 : 0 < r) (h1 : r < 19) : Canon 5 133 13 (RB r) :=
  CertificateChecks.KernelHNLocal.canon_of_valid
    (CertificateChecks.KernelHNLocal.rootsOK_spec 19 roots r h0 h1)

theorem mat_T {g G : ℕ} (hg : g < 18) (h : Nat.beq G (trM (RB (g + 1))) = true) :
    Canon 5 133 13 G ∧ matJ (cEl g) = (OM G)ᵀ := by
  have hc := CertificateChecks.KernelHNLocal.tp_sound (canon_RB (r := g + 1) (by omega) (by omega)) h
  refine ⟨hc.1, ?_⟩
  rw [hc.2, Matrix.transpose_transpose]
  exact mat_cEl g hg

theorem fix_of {g G V : ℕ} (hT : Canon 5 133 13 G ∧ matJ (cEl g) = (OM G)ᵀ) (hV : V < 2 ^ 399)
    (h : fixVec CFSG.KD.HNLocal.MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.HNLocal.CM3
      CFSG.KD.OrdHN.RM G V = true) : matJ (cEl g) *ᵥ cv V = cv V := by
  rw [hT.2]
  exact (CFSG.KS.HNLocal.fixVec_sound CertificateChecks.KernelHNLocal.consts
    CFSG.KD.HNLocal.masks CFSG.KD.HNLocal.cm hT.1 hV h).2

theorem V_lt : V0 < 2 ^ 399 ∧ V1 < 2 ^ 399 ∧ V2 < 2 ^ 399 := by decide +kernel

@[expose] noncomputable def vfix (v : Vec) : Subgroup JH where
  carrier := {g | matJ g *ᵥ v = v}
  one_mem' := Matrix.one_mulVec v
  mul_mem' {x y} hx hy := by
    have hx' : matJ x *ᵥ v = v := hx
    have hy' : matJ y *ᵥ v = v := hy
    change (matJ x * matJ y) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec, hy', hx']
  inv_mem' {x} hx := by
    have hx' : matJ x *ᵥ v = v := hx
    change matJ x⁻¹ *ᵥ v = v
    have e : matJ x⁻¹ * matJ x = 1 := by
      change matJ (x⁻¹ * x) = 1
      rw [inv_mul_cancel]
      rfl
    calc matJ x⁻¹ *ᵥ v = matJ x⁻¹ *ᵥ (matJ x *ᵥ v) := by rw [hx']
      _ = v := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]

theorem mem_vfix {g : JH} {v : Vec} : g ∈ vfix v ↔ matJ g *ᵥ v = v := Iff.rfl

theorem fix_closure {S : Set JH} {v : Vec} (h : ∀ x ∈ S, matJ x *ᵥ v = v) {g : JH}
    (hg : g ∈ Subgroup.closure S) : matJ g *ᵥ v = v :=
  mem_vfix.1 ((Subgroup.closure_le (vfix v)).2 (fun x hx => mem_vfix.2 (h x hx)) hg)

theorem matJ_mul (x y : JH) : matJ (x * y) = matJ x * matJ y := rfl

theorem reach2 {XC TD : Nat → Nat} {N NL GA GB : Nat} {g0 g1 : JH}
    (h0 : Canon 5 133 13 GA ∧ matJ g0 = (OM GA)ᵀ) (h1 : Canon 5 133 13 GB ∧ matJ g1 = (OM GB)ᵀ)
    (hleaf : ∀ j < NL, TL XC TD N GA GB j < 2 ^ 50) (ht0 : TD 0 % 2 ^ 21 = 1)
    (htn : TD NL % 2 ^ 21 = N) (hNL : N ≤ 133 * NL) (hX : ∀ i < NL, XC i < 2 ^ 53200)
    (hrp : ∀ k < N, 0 < recX XC MM k) :
    ∀ k < N, ∃ w ∈ Subgroup.closure ({g0, g1} : Set JH),
      matJ w *ᵥ cv (recX XC MM 0) = cv (recX XC MM k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, Subgroup.one_mem _, Matrix.one_mulVec _⟩
    · obtain ⟨p, hp, -, hv⟩ := tree_child h0.1 h1.1 hleaf ht0 htn hNL hX hrp hpos hk
      obtain ⟨w, hw, he⟩ := ih p hp (by omega)
      rcases hv with hv | hv
      · refine ⟨g0 * w, Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hw, ?_⟩
        rw [matJ_mul, ← Matrix.mulVec_mulVec, he, h0.2, hv]
      · refine ⟨g1 * w, Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hw, ?_⟩
        rw [matJ_mul, ← Matrix.mulVec_mulVec, he, h1.2, hv]

theorem canon2 {XC TD : Nat → Nat} {N NL GA GB : Nat} (hGA : Canon 5 133 13 GA)
    (hGB : Canon 5 133 13 GB) (hleaf : ∀ j < NL, TL XC TD N GA GB j < 2 ^ 50)
    (ht0 : TD 0 % 2 ^ 21 = 1) (htn : TD NL % 2 ^ 21 = N) (hNL : N ≤ 133 * NL)
    (hX : ∀ i < NL, XC i < 2 ^ 53200) (hrp : ∀ k < N, 0 < recX XC MM k)
    (hc0 : CFSG.KS.HNLocal.CCanon (recX XC MM 0))
    {k : ℕ} (hk : k < N) : CFSG.KS.HNLocal.CCanon (recX XC MM k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact hc0
  · exact (tree_child hGA hGB hleaf ht0 htn hNL hX hrp hpos hk).choose_spec.2.1

theorem land_mod21 (x : ℕ) : Nat.land x 2097151 = x % 2 ^ 21 := by
  rw [show (2097151 : ℕ) = 2 ^ 21 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_eq_mod x 21

theorem level_of {l N : ℕ} {x : ℕ → Vec} {K : Subgroup JH}
    (hx0 : x 0 = PK (chainPt (l + 1)).val)
    (hK : ∀ g ∈ K, ∀ i ≤ l, matJ g *ᵥ PK (chainPt i).val = PK (chainPt i).val)
    (hreach : ∀ k < N, ∃ w ∈ K, matJ w *ᵥ x 0 = x k)
    (hinj : ∀ i < N, ∀ j < N, x i = x j → i = j) :
    ∃ f : Fin N → JH, (∀ k, ∀ i ≤ l, f k • chainPt i = chainPt i) ∧
      Function.Injective fun k => f k • chainPt (l + 1) := by
  choose w hwK hw using hreach
  refine ⟨fun k => w k.val k.isLt, fun k i hi => ?_, fun k k' e => ?_⟩
  · refine Fin.ext (PK_injective _ (w k.val k.isLt • chainPt i).isLt _ (chainPt i).isLt ?_)
    rw [PK_smul]
    exact hK _ (hwK _ _) i hi
  · have e' := congrArg (fun y : X => PK y.val) e
    simp only at e'
    rw [PK_smul, PK_smul, ← hx0, hw, hw] at e'
    exact Fin.ext (hinj _ k.isLt _ k'.isLt e')

theorem vec_inj {XC : Nat → Nat} {N : ℕ} (hc : ∀ k < N, CFSG.KS.HNLocal.CCanon (recX XC MM k))
    (h : ∀ i < N, ∀ j < N, recX XC MM i = recX XC MM j → i = j) :
    ∀ i < N, ∀ j < N, cv (recX XC MM i) = cv (recX XC MM j) → i = j := fun i hi j hj e =>
  h i hi j hj (CFSG.KS.HNLocal.cvec_inj (hc i hi) (hc j hj) e)

theorem g10 : Canon 5 133 13 G10 ∧ matJ (cEl 0) = (OM G10)ᵀ := mat_T (by norm_num) tp.c0
theorem g11 : Canon 5 133 13 G11 ∧ matJ (cEl 11) = (OM G11)ᵀ := mat_T (by norm_num) tp.c1
theorem g20 : Canon 5 133 13 G20 ∧ matJ (cEl 12) = (OM G20)ᵀ := mat_T (by norm_num) tp.c2
theorem g21 : Canon 5 133 13 G21 ∧ matJ (cEl 13) = (OM G21)ᵀ := mat_T (by norm_num) tp.c3
theorem g30 : Canon 5 133 13 G30 ∧ matJ (cEl 14) = (OM G30)ᵀ := mat_T (by norm_num) tp.c4
theorem g31 : Canon 5 133 13 G31 ∧ matJ (cEl 15) = (OM G31)ᵀ := mat_T (by norm_num) tp.c5
theorem g32 : Canon 5 133 13 G32 ∧ matJ (cEl 16) = (OM G32)ᵀ := mat_T (by norm_num) tp.c6
theorem g33 : Canon 5 133 13 G33 ∧ matJ (cEl 17) = (OM G33)ᵀ := mat_T (by norm_num) tp.c7

theorem leaf1 : ∀ j < 79, TL XC1 TD1 10395 G10 G11 j < 2 ^ 50 := leaf_lt tr1 (by norm_num)
theorem leaf2 : ∀ j < 6, TL XC2 TD2 720 G20 G21 j < 2 ^ 50 := leaf_lt tr2 (by norm_num)

theorem td1 : TD1 0 % 2 ^ 21 = 1 ∧ TD1 79 % 2 ^ 21 = 10395 :=
  ⟨by rw [← land_mod21]; exact Nat.eq_of_beq_eq_true td0_1,
    by rw [← land_mod21]; exact Nat.eq_of_beq_eq_true tdn_1⟩

theorem td2 : TD2 0 % 2 ^ 21 = 1 ∧ TD2 6 % 2 ^ 21 = 720 :=
  ⟨by rw [← land_mod21]; exact Nat.eq_of_beq_eq_true td0_2,
    by rw [← land_mod21]; exact Nat.eq_of_beq_eq_true tdn_2⟩

theorem x01 : recX XC1 MM 0 = V1 := Nat.eq_of_beq_eq_true x0_1
theorem x02 : recX XC2 MM 0 = V2 := Nat.eq_of_beq_eq_true x0_2
theorem x03 : recX XC3 MM 0 = V3 := Nat.eq_of_beq_eq_true x0_3

theorem xc1_lt : ∀ i < 79, XC1 i < 2 ^ 53200 := chunks_lt (by quickRfl)
theorem xc2_lt : ∀ i < 6, XC2 i < 2 ^ 53200 := chunks_lt (by quickRfl)

theorem xc1_pos : ∀ k < 10395, 0 < recX XC1 MM k := tree_pos (by norm_num) so1 (by quickRfl)
theorem xc2_pos : ∀ k < 720, 0 < recX XC2 MM k := tree_pos (by norm_num) so2 (by quickRfl)

theorem level1 : ∃ f : Fin 10395 → JH, (∀ k, ∀ i ≤ 0, f k • chainPt i = chainPt i) ∧
    Function.Injective fun k => f k • chainPt (0 + 1) := by
  refine level_of (x := fun k => cv (recX XC1 MM k)) (K := Subgroup.closure {cEl 0, cEl 11})
    (by change cv (recX XC1 MM 0) = PK (chainPt 1).val; rw [x01, PK_c1]) (fun g hg i hi => ?_)
    (reach2 g10 g11 leaf1 td1.1 td1.2 (by norm_num) xc1_lt xc1_pos)
    (vec_inj (fun k hk => canon2 g10.1 g11.1 leaf1 td1.1 td1.2 (by norm_num) xc1_lt xc1_pos
      (by rw [x01]; exact V_canon.2.1) hk) (tree_inj (by norm_num) so1))
  obtain rfl : i = 0 := by omega
  rw [PK_c0]
  refine fix_closure ?_ hg
  rintro _ (rfl | rfl)
  · exact fix_of g10 V_lt.1 fx.c0
  · exact fix_of g11 V_lt.1 fx.c1

theorem level2 : ∃ f : Fin 720 → JH, (∀ k, ∀ i ≤ 1, f k • chainPt i = chainPt i) ∧
    Function.Injective fun k => f k • chainPt (1 + 1) := by
  refine level_of (x := fun k => cv (recX XC2 MM k)) (K := Subgroup.closure {cEl 12, cEl 13})
    (by change cv (recX XC2 MM 0) = PK (chainPt 2).val; rw [x02, PK_c2]) (fun g hg i hi => ?_)
    (reach2 g20 g21 leaf2 td2.1 td2.2 (by norm_num) xc2_lt xc2_pos)
    (vec_inj (fun k hk => canon2 g20.1 g21.1 leaf2 td2.1 td2.2 (by norm_num) xc2_lt xc2_pos
      (by rw [x02]; exact V_canon.2.2.1) hk) (tree_inj (by norm_num) so2))
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [PK_c0]
    refine fix_closure ?_ hg
    rintro _ (rfl | rfl)
    · exact fix_of g20 V_lt.1 fx.c2
    · exact fix_of g21 V_lt.1 fx.c4
  · rw [PK_c1]
    refine fix_closure ?_ hg
    rintro _ (rfl | rfl)
    · exact fix_of g20 V_lt.2.1 fx.c3
    · exact fix_of g21 V_lt.2.1 fx.c5

theorem par3 : ∀ k, 1 ≤ k → k < 32 → PAR3.getD (k - 1) 0 % 64 < k ∧ PAR3.getD (k - 1) 0 / 64 < 4 ∧
    PI (PAR3.getD (k - 1) 0 / 64) (PAR3.getD (k - 1) 0 % 64) = k := by
  decide +kernel

noncomputable abbrev e3 (s : ℕ) : JH := cEl (14 + s)

theorem act3 {s : ℕ} (hs : s < 4) : ∀ r < 32, PI s r < 32 ∧ CFSG.KS.HNLocal.CCanon (recX XC3 MM (PI s r)) ∧
    cv (recX XC3 MM (PI s r)) = matJ (e3 s) *ᵥ cv (recX XC3 MM r) := by
  have key : ∀ {G : ℕ}, (Canon 5 133 13 G ∧ matJ (e3 s) = (OM G)ᵀ) →
      actLeaf XC3 (PI s) MM CFSG.KD.HNLocal.MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H
        CFSG.KD.HNLocal.CM3 CFSG.KD.OrdHN.RM 32 G 0 32 = true →
      ∀ r < 32, PI s r < 32 ∧ CFSG.KS.HNLocal.CCanon (recX XC3 MM (PI s r)) ∧
        cv (recX XC3 MM (PI s r)) = matJ (e3 s) *ᵥ cv (recX XC3 MM r) := by
    intro G hT h r hr
    have := CFSG.KS.HNLocal.actLeaf_sound CertificateChecks.KernelHNLocal.consts
      CFSG.KD.HNLocal.masks CFSG.KD.HNLocal.cm hT.1 (by norm_num) h r hr
    simp only [Nat.mul_zero, Nat.zero_add] at this
    rw [hT.2]
    exact this
  interval_cases s
  · exact key g30 act.c0
  · exact key g31 act.c1
  · exact key g32 act.c2
  · exact key g33 act.c3

theorem e3_mem {s : ℕ} (hs : s < 4) :
    e3 s ∈ Subgroup.closure ({cEl 14, cEl 15, cEl 16, cEl 17} : Set JH) := by
  apply Subgroup.subset_closure
  interval_cases s <;> simp [e3]

theorem reach3 : ∀ k < 32, ∃ w ∈ Subgroup.closure ({cEl 14, cEl 15, cEl 16, cEl 17} : Set JH),
    matJ w *ᵥ cv (recX XC3 MM 0) = cv (recX XC3 MM k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, Subgroup.one_mem _, Matrix.one_mulVec _⟩
    · obtain ⟨hp, hs, he⟩ := par3 k hpos hk
      obtain ⟨w, hw, hwe⟩ := ih _ hp (by omega)
      refine ⟨e3 (PAR3.getD (k - 1) 0 / 64) * w, Subgroup.mul_mem _ (e3_mem hs) hw, ?_⟩
      have h := (act3 hs (PAR3.getD (k - 1) 0 % 64) (by omega)).2.2
      rw [he] at h
      rw [matJ_mul, ← Matrix.mulVec_mulVec, hwe, h]

theorem canon3 {k : ℕ} (hk : k < 32) : CFSG.KS.HNLocal.CCanon (recX XC3 MM k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [x03]
    exact V_canon.2.2.2
  · obtain ⟨hp, hs, he⟩ := par3 k hpos hk
    have h := (act3 hs (PAR3.getD (k - 1) 0 % 64) (by omega)).2.1
    rwa [he] at h

theorem inj3 : ∀ i < 32, ∀ j < 32, recX XC3 MM i = recX XC3 MM j → i = j := by
  have so3' : sortLeaf XC3 SD3 32 MM 0 = true := so3
  have hs := CFSG.KS.HNLocal.sortLeaf_spec so3'
  apply CertificateChecks.KernelHNLocal.injOn_of_order (σ := sig SD3)
  · intro _
    have := hs.1 (by norm_num)
    simpa using this
  · intro i hi
    have h' := hs.2 i (by omega) (by omega)
    simpa using h'

theorem level3 : ∃ f : Fin 32 → JH, (∀ k, ∀ i ≤ 2, f k • chainPt i = chainPt i) ∧
    Function.Injective fun k => f k • chainPt (2 + 1) := by
  refine level_of (x := fun k => cv (recX XC3 MM k))
    (K := Subgroup.closure {cEl 14, cEl 15, cEl 16, cEl 17})
    (by change cv (recX XC3 MM 0) = PK (chainPt 3).val; rw [x03, PK_c3]) (fun g hg i hi => ?_)
    reach3 (vec_inj (fun k hk => canon3 hk) inj3)
  have key : ∀ {V : ℕ}, V < 2 ^ 399 → (∀ s < 4, matJ (e3 s) *ᵥ cv V = cv V) →
      matJ g *ᵥ cv V = cv V := by
    intro V _ hV
    refine fix_closure ?_ hg
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hV 0 (by norm_num)
    · exact hV 1 (by norm_num)
    · exact hV 2 (by norm_num)
    · exact hV 3 (by norm_num)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · rw [PK_c0]
    refine key V_lt.1 fun s hs => ?_
    interval_cases s
    · exact fix_of g30 V_lt.1 fx.c6
    · exact fix_of g31 V_lt.1 fx.c9
    · exact fix_of g32 V_lt.1 fx.c12
    · exact fix_of g33 V_lt.1 fx.c15
  · rw [PK_c1]
    refine key V_lt.2.1 fun s hs => ?_
    interval_cases s
    · exact fix_of g30 V_lt.2.1 fx.c7
    · exact fix_of g31 V_lt.2.1 fx.c10
    · exact fix_of g32 V_lt.2.1 fx.c13
    · exact fix_of g33 V_lt.2.1 fx.c16
  · rw [PK_c2]
    refine key V_lt.2.2 fun s hs => ?_
    interval_cases s
    · exact fix_of g30 V_lt.2.2 fx.c8
    · exact fix_of g31 V_lt.2.2 fx.c11
    · exact fix_of g32 V_lt.2.2 fx.c14
    · exact fix_of g33 V_lt.2.2 fx.c17

theorem levelFacts : LevelFacts := by
  intro l hl
  interval_cases l
  · exact level1
  · exact level2
  · exact level3

end CertificateChecks.KernelHNChain

end
