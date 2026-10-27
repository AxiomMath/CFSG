module

public import CFSG.Sporadic.Ly.SeedGroup
public import CFSG.Certificates.Kernel.Fam.CentSound
public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.Fam.LyAlg.Checks.P
import CFSG.Certificates.Kernel.Fam.LyAlg.Checks.B
import CFSG.Certificates.Kernel.Fam.LyAlg.Checks.C
import CFSG.Certificates.Kernel.Fam.LyAlg.Checks.D
import CFSG.Certificates.Kernel.Fam.LyAlg.Checks.K
import Certificates.Kernel.Ly3085.Bytes
import Certificates.Kernel.Sporadic.OrdCommon
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.KS.Cent CFSG.KC.LQT.SecS CFSG.Sporadic.Ly
open CFSG.KD.FamLyAlg Matrix

local notation "OM" => ordMat 5 111 12 1332

theorem a_mA : sA = OM (RW 1) := by
  have h := seed_sound (hnb := rfl) consts alg1_bytes (by decide) d1 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed1 = _
  rw [CFSG.KD.BrLy.LySeedA.eq, h]

theorem a_mB : sB = OM (RW 2) := by
  have h := seed_sound (hnb := rfl) consts alg2_bytes (by decide) d2 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed2 = _
  rw [CFSG.KD.BrLy.LySeedB.eq, h]

theorem a_v1 : validM 5 147852 L H (RW 1) = true := (andT' (andT' d1_end).2).2

theorem a_v2 : validM 5 147852 L H (RW 2) = true := (andT' (andT' d2_end).2).2

theorem a_prod {r x y : Nat} (hx : validM 5 147852 L H (RW x) = true)
    (hy : validM 5 147852 L H (RW y) = true) (h : Nat.beq (RW r) (mul (RW x) (RW y)) = true) :
    validM 5 147852 L H (RW r) = true ∧ OM (RW r) = OM (RW x) * OM (RW y) := by
  rw [Nat.eq_of_beq_eq_true h]
  exact mul_sound' (hnb := rfl) consts hx hy

theorem a_canon {r : Nat} (h : validM 5 147852 L H (RW r) = true) : Canon 5 111 12 (RW r) :=
  validM_canon consts h

theorem a_lincomb {Ls : List Nat} {C : Nat}
    (h : Nat.beq (CFSG.KC.Fam.lincomb RW 5 12 8 L H RWn Ls) C = true)
    (hL : ∀ x ∈ Ls, Nat.land x 255 < 5 ∧ regBelow (Nat.shiftRight x 8) RWn = true ∧
      Canon 5 111 12 (RW (Nat.shiftRight x 8))) :
    Canon 5 111 12 C ∧ OM C = (Ls.map fun x => ((Nat.land x 255 : Nat) : ZMod 5) •
      OM (RW (Nat.shiftRight x 8))).sum := by
  rw [← Nat.eq_of_beq_eq_true h]
  exact lincomb_sound consts (by norm_num) Ls hL

theorem alg_C (M : Matrix (Fin 111) (Fin 111) (ZMod 5)) (cA : Commute M (OM (RW 1)))
    (cB : Commute M (OM (RW 2))) : Canon 5 111 12 Cm ∧ Commute M (OM Cm) := by
  obtain ⟨v5, e5⟩ := a_prod a_v2 a_v1 p_5
  obtain ⟨v6, e6⟩ := a_prod v5 a_v2 p_6
  obtain ⟨v7, e7⟩ := a_prod v6 a_v1 p_7
  obtain ⟨v8, e8⟩ := a_prod a_v2 a_v1 p_8
  obtain ⟨v9, e9⟩ := a_prod a_v1 a_v2 p_9
  obtain ⟨v10, e10⟩ := a_prod v9 a_v2 p_10
  obtain ⟨v11, e11⟩ := a_prod v10 a_v1 p_11
  obtain ⟨v12, e12⟩ := a_prod a_v2 a_v2 p_12
  have c5 : Commute M (OM (RW 5)) := by rw [e5]; exact cB.mul_right cA
  have c6 : Commute M (OM (RW 6)) := by rw [e6]; exact c5.mul_right cB
  have c7 : Commute M (OM (RW 7)) := by rw [e7]; exact c6.mul_right cA
  have c8 : Commute M (OM (RW 8)) := by rw [e8]; exact cB.mul_right cA
  have c9 : Commute M (OM (RW 9)) := by rw [e9]; exact cA.mul_right cB
  have c10 : Commute M (OM (RW 10)) := by rw [e10]; exact c9.mul_right cB
  have c11 : Commute M (OM (RW 11)) := by rw [e11]; exact c10.mul_right cA
  have c12 : Commute M (OM (RW 12)) := by rw [e12]; exact cB.mul_right cB
  obtain ⟨cCm, eCm⟩ := a_lincomb comb (by
      intro x hx
      have hn : RWn = 13 := Nat.eq_of_beq_eq_true nreg
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by rw [hn]; decide, a_canon v7⟩
      · exact ⟨by decide, by rw [hn]; decide, a_canon v8⟩
      · exact ⟨by decide, by rw [hn]; decide, a_canon a_v2⟩
      · exact ⟨by decide, by rw [hn]; decide, a_canon v11⟩
      · exact ⟨by decide, by rw [hn]; decide, a_canon v12⟩)
  refine ⟨cCm, ?_⟩
  rw [eCm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  exact ((((c7.smul_right _).add_right ((c8.smul_right _).add_right ((cB.smul_right _).add_right
    ((c11.smul_right _).add_right ((c12.smul_right _).add_right (Commute.zero_right M))))))))

noncomputable abbrev vC : Fin 111 → ZMod 5 := fun i => OM C0v i ⟨0, by norm_num⟩

theorem alg_ker : OM Cm *ᵥ vC = 0 ∧
    OM Ym * OM Cm + Matrix.vecMulVec vC (toVec 5 111 12 uprow) = 1 := by
  obtain ⟨cCm, -⟩ := alg_C 1 (Commute.one_left _) (Commute.one_left _)
  obtain ⟨cC0, -, hrk⟩ := rker_sound consts (by norm_num) (hnb := rfl) cCm rker
  refine ⟨?_, hrk⟩
  have hnull : OM Cm * OM C0v = 0 := by
    rw [← (mulR_sound consts cCm cC0).2, Nat.eq_of_beq_eq_true rnull, ordMat_zero]
  funext i
  have := congrFun (congrFun hnull i) ⟨0, by norm_num⟩
  rw [Matrix.mul_apply] at this
  exact this

theorem alg_eig (M : Matrix (Fin 111) (Fin 111) (ZMod 5)) (cC : Commute M (OM Cm)) :
    M *ᵥ vC = (toVec 5 111 12 uprow ⬝ᵥ (M *ᵥ vC)) • vC := by
  obtain ⟨hv, hrk⟩ := alg_ker
  have hCx : OM Cm *ᵥ (M *ᵥ vC) = 0 := by
    rw [Matrix.mulVec_mulVec, ← cC.eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h1 := congrArg (fun N => N *ᵥ (M *ᵥ vC)) hrk
  simp only [Matrix.one_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hCx,
    Matrix.mulVec_zero, zero_add] at h1
  calc M *ᵥ vC = Matrix.vecMulVec vC (toVec 5 111 12 uprow) *ᵥ (M *ᵥ vC) := h1.symm
    _ = _ := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring

theorem alg_vrow : toVec 5 111 12 vrow = vC := by
  funext i
  simp only [vC, Nat.eq_of_beq_eq_true vrowcol, colOf_apply consts]
  simp [toVec]

theorem alg_tree (M : Matrix (Fin 111) (Fin 111) (ZMod 5)) (cA : Commute M (OM (RW 1)))
    (cB : Commute M (OM (RW 2))) (c : ZMod 5) (hv : M *ᵥ vC = c • vC) :
    ∀ i < 111, M *ᵥ toVec 5 111 12 (Vc i) = c • toVec 5 111 12 (Vc i) := by
  obtain ⟨-, cAT, eAT⟩ := tpose_sound consts (hnb := rfl) tpose1
  obtain ⟨-, cBT, eBT⟩ := tpose_sound consts (hnb := rfl) tpose2
  obtain ⟨hVc, -⟩ := rowsBasis_sound' consts (hnb := rfl) basisc
  have hV0 : Vc 0 = vrow := Nat.eq_of_beq_eq_true (andT' treec).1
  have hv0 : VCanon 5 111 12 vrow := by
    rw [← hV0]
    exact hVc 0 (by norm_num)
  have hQ0 : M *ᵥ toVec 5 111 12 vrow = c • toVec 5 111 12 vrow := by
    rw [alg_vrow]
    exact hv
  intro i hi
  refine (treeVec_sound consts hv0 cAT cBT treec (fun y => M *ᵥ y = c • y) hQ0 ?_ i hi).2
  intro y hy
  rw [eAT, eBT, Matrix.vecMul_transpose, Matrix.vecMul_transpose]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, cA.eq, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul]
  · rw [Matrix.mulVec_mulVec, cB.eq, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul]

theorem alg_rows (M : Matrix (Fin 111) (Fin 111) (ZMod 5)) (c : ZMod 5)
    (h : ∀ i < 111, M *ᵥ toVec 5 111 12 (Vc i) = c • toVec 5 111 12 (Vc i)) :
    Matrix.of (fun i j : Fin 111 => toVec 5 111 12 (Vc i.val) j) * Mᵀ =
      c • Matrix.of (fun i j : Fin 111 => toVec 5 111 12 (Vc i.val) j) := by
  funext i j
  have := congrFun (h i.val i.isLt) j
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem scalar_of_rows {n : Type*} [Fintype n] [DecidableEq n] {R Ri M : Matrix n n (ZMod 5)}
    {c : ZMod 5} (hR : R * Ri = 1) (hRM : R * Mᵀ = c • R) : M = c • 1 := by
  have hRi := mul_eq_one_comm.mp hR
  have hT : Mᵀ = c • 1 := by
    calc Mᵀ = Ri * R * Mᵀ := by rw [hRi, Matrix.one_mul]
      _ = c • 1 := by rw [Matrix.mul_assoc, hRM, Matrix.mul_smul, hRi]
  have := congrArg Matrix.transpose hT
  rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at this

theorem alg_basis (M : Matrix (Fin 111) (Fin 111) (ZMod 5)) (c : ZMod 5)
    (h : ∀ i < 111, M *ᵥ toVec 5 111 12 (Vc i) = c • toVec 5 111 12 (Vc i)) : M = c • 1 :=
  scalar_of_rows (rowsBasis_sound' consts (hnb := rfl) basisc).2 (alg_rows M c h)

theorem commutant_scalar : ∀ M : Matrix (Fin 111) (Fin 111) (ZMod 5), M * sA = sA * M →
    M * sB = sB * M → ∃ c : ZMod 5, M = c • 1 := by
  intro M hA hB
  rw [a_mA] at hA
  rw [a_mB] at hB
  have cA : Commute M (OM (RW 1)) := hA
  have cB : Commute M (OM (RW 2)) := hB
  obtain ⟨-, cC⟩ := alg_C M cA cB
  exact ⟨_, alg_basis M _ (alg_tree M cA cB _ (alg_eig M cC))⟩

end CertificateChecks.KernelLy

end
