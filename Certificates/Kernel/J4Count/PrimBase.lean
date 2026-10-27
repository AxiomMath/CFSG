
module

public import Certificates.Kernel.J4Count.PrimData
public import Certificates.Kernel.J4Count.FixCEEltBase
public import Certificates.Kernel.J4Count.HOrderBase
public import Certificates.Kernel.J4Hub.Card
public import CFSG.Sporadic.J4.Simple
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Count.Suborb
public import CFSG.Certificates.Kernel.J4FixCESound
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Kernel.J4Count.FixCEChecks
public import Certificates.Kernel.J4Count.StarsBase
public import Certificates.Kernel.J4Q.C4025
public import Certificates.Kernel.J4Q.QT2AC

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Prim

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT MulAction
open CFSG.Sporadic.J4Schreier (H v rootBits)
open CFSG.KD.J4Prim
open CFSG.KC.J4Q (vecJ)
open CFSG.KD.J4Q (rm Ai Bi)
open CertificateChecks.KernelJ4Count.FixCE (PR PR_of inv_smul_PR)
open CertificateChecks.KernelJ4Count (ncard_orbit_mem mem_orbit_of_ncard qv qv_mem exists_sz sz_zero
  qv_zero L7 stabilizer_v_eq_Hj' stabilizer_v H_eq_Hj' card_Hj')
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_xor toVecD_zero)
open scoped Matrix

@[expose] noncomputable def treeOK : Bool :=
  Nat.beq PTS[0]! rootBits && (List.range 112).all fun k =>
    Nat.blt PTS[k]! (2 ^ 112) && (Nat.beq k 0 || (Nat.blt PAR[k]! k &&
      Nat.beq PTS[k]! (vecJ rm PTS[PAR[k]!]! (if Nat.beq LET[k]! 0 then Ai else Bi))))

theorem treeOK_true : treeOK = true := by quickRfl

@[expose] def selX (m : ℕ) : ℕ :=
  (List.range 112).foldl (fun acc i => if m.testBit i then acc ^^^ PTS[i]! else acc) 0

@[expose] def spanOK : Bool := (List.range 112).all fun j => Nat.beq (selX MSK[j]!) (2 ^ j)

theorem spanOK_true : spanOK = true := by quickRfl

theorem tree_parts {k : ℕ} (hk : k < 112) : PTS[k]! < 2 ^ 112 ∧ (k = 0 ∨ (PAR[k]! < k ∧
    PTS[k]! = vecJ rm PTS[PAR[k]!]! (if LET[k]! = 0 then Ai else Bi))) := by
  have h := treeOK_true
  unfold treeOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.2 k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h2
  obtain ⟨h3, h4⟩ := h2
  refine ⟨h3, ?_⟩
  rcases h4 with h4 | ⟨h5, h6⟩
  · exact Or.inl h4
  · right
    exact ⟨h5, h6⟩

theorem pts_zero : PTS[0]! = rootBits := by
  have h := treeOK_true
  unfold treeOK at h
  rw [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem span_parts {j : ℕ} (hj : j < 112) : selX MSK[j]! = 2 ^ j := by
  have h := spanOK_true
  unfold spanOK at h
  rw [List.all_eq_true] at h
  exact Nat.eq_of_beq_eq_true (h j (List.mem_range.2 hj))

noncomputable abbrev rho (p : ℕ) : Row := toRow (toVecD 112 p)

theorem PR_Ai : PR (a⁻¹ : J) Ai :=
  PR_of (m := Ai) (CertificateChecks.KernelJ4Q.base_invs 0) (Mx_a_inv CertificateChecks.KernelJ4Q.matFacts)

theorem PR_Bi : PR (b⁻¹ : J) Bi :=
  PR_of (m := Bi) (CertificateChecks.KernelJ4Q.base_invs 1) (Mx_b_inv CertificateChecks.KernelJ4Q.matFacts)

theorem pts_mem : ∀ k < 112, rho PTS[k]! ∈ orbit J v := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨-, h0 | ⟨hpk, he⟩⟩ := tree_parts hk
    · subst h0
      rw [pts_zero]
      exact mem_orbit_self v
    · obtain ⟨g, hg⟩ := ih _ hpk (by omega)
      change g • v = rho PTS[PAR[k]!]! at hg
      have hp := (tree_parts (k := PAR[k]!) (by omega)).1
      by_cases hl : LET[k]! = 0
      · rw [if_pos hl] at he
        refine ⟨a * g, ?_⟩
        have e := inv_smul_PR PR_Ai hp
        rw [inv_inv] at e
        change (a * g) • v = rho PTS[k]!
        rw [mul_smul, hg, e, ← he]
      · rw [if_neg hl] at he
        refine ⟨b * g, ?_⟩
        have e := inv_smul_PR PR_Bi hp
        rw [inv_inv] at e
        change (b * g) • v = rho PTS[k]!
        rw [mul_smul, hg, e, ← he]

theorem toVecD_two_pow {j : ℕ} (hj : j < 112) :
    toVecD 112 (2 ^ j) = Pi.single (⟨j, hj⟩ : Fin 112) 1 := by
  funext i
  rw [toVecD_apply, Nat.testBit_two_pow]
  by_cases h : i = ⟨j, hj⟩
  · subst h
    simp
  · have h' : j ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h', Pi.single_apply, h]

theorem eq_one_of_fix {g : J} (h : ∀ k < 112, g • rho PTS[k]! = rho PTS[k]!) : g = 1 := by
  set N : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
    (((g⁻¹ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) with hN
  have hfix : ∀ k < 112, toVecD 112 PTS[k]! ᵥ* N = toVecD 112 PTS[k]! := by
    intro k hk
    have := congrArg ofRow (h k hk)
    rw [smul_row] at this
    exact this
  have hsel : ∀ m, toVecD 112 (selX m) ᵥ* N = toVecD 112 (selX m) := by
    intro m
    unfold selX
    rw [CFSG.Sporadic.SmallF2.foldl_xor_toVecD, toVecD_zero, zero_add, Matrix.sum_vecMul]
    refine Finset.sum_congr rfl fun i hi => ?_
    split_ifs
    · exact hfix i (Finset.mem_range.1 hi)
    · exact Matrix.zero_vecMul _
  have hrow : ∀ i : Fin 112, N i = Pi.single i 1 := by
    intro i
    have e := hsel MSK[i.val]!
    rw [span_parts i.isLt, toVecD_two_pow i.isLt, Matrix.single_one_vecMul] at e
    exact e
  have hN1 : N = 1 := by
    funext i j
    rw [hrow i, Matrix.one_apply, Pi.single_apply]
    by_cases hij : j = i
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have : g⁻¹ = 1 := eq_one_of_val hN1
  exact inv_eq_one.1 this

instance rowFinite' : Finite Row := inferInstanceAs (Finite (Fin 112 → ZMod 2))

abbrev X : Type := ↥(orbit J v)

noncomputable instance : Fintype X := Fintype.ofFinite X

abbrev x0 : X := ⟨v, mem_orbit_self v⟩

theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [CertificateChecks.KernelJ4Hub.card_J']; norm_num)

instance : FaithfulSMul J X := by
  refine ⟨fun {g₁ g₂} h => ?_⟩
  have e : g₂⁻¹ * g₁ = 1 := by
    refine eq_one_of_fix fun k hk => ?_
    have := congrArg Subtype.val (h ⟨_, pts_mem k hk⟩)
    change g₁ • rho PTS[k]! = g₂ • rho PTS[k]! at this
    rw [mul_smul, this, inv_smul_smul]
  rw [← mul_left_cancel_iff (a := g₂⁻¹), e, inv_mul_cancel]

theorem L7_iff (x : ℕ) : x ∈ L7 ↔ ∃ i : Fin 7, subSizesF i = x := by
  constructor
  · intro hx
    simp only [L7, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [subSizesF, L7]

theorem subSizesF_inj : Function.Injective subSizesF := by decide

theorem ab_pow' (hM : MatFacts) : ((a : J) * b) ^ 37 = 1 := by
  apply eq_one_of_val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul, a_coe,
    b_coe, gA_val hM, gB_val hM]
  have := congrArg rowsMatrix (eqRows_iff.1 hM.ab37)
  rwa [rowsMatrix_powRows, rowsMatrix_mulRows, rowsMatrix_rowsA, rowsMatrix_rowsB,
    rowsMatrix_idRows] at this

theorem cJ_val' (hM : MatFacts) :
    (((cJ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) =
      rowsMatrix conjRows := (conjRows_spec hM).symm

theorem cJ_inv_val' (hM : MatFacts) :
    (((cJ⁻¹ : J) : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) =
      rowsMatrix (invRows conjRows) := by
  have hc : rowsMatrix conjRows * rowsMatrix (invRows conjRows) = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 hM.cinv)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  rw [InvMemClass.coe_inv, Matrix.coe_units_inv, cJ_val' hM]
  exact Matrix.inv_eq_right_inv hc

theorem z_pow' (hM : MatFacts) : ((a : J) * (cJ⁻¹ * (a * b) * cJ)) ^ 43 = 1 := by
  apply eq_one_of_val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [cJ_inv_val' hM, cJ_val' hM, a_coe, b_coe, gA_val hM, gB_val hM]
  have := congrArg rowsMatrix (eqRows_iff.1 hM.z43)
  rw [rowsMatrix_powRows, zRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_mulRows, rowsMatrix_rowsA, rowsMatrix_rowsB, rowsMatrix_idRows] at this
  rw [← this]
  simp only [Matrix.mul_assoc]

end CertificateChecks.KernelJ4Count.Prim

end
