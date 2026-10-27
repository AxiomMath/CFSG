module

public import Certificates.Kernel.Misc.Perm.J2Rel
public import Certificates.Data.Inputs2324QJ2
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
open CertificateChecks.KernelMisc.J2C3 (cm I)

@[expose] noncomputable def prodVG (w : List ℕ) : ℕ := w.foldr (fun j p => cm (VG j) p) I

theorem rJV {j : ℕ} (hj : j < 6) : R (j2VArr j) (VG j) := by
  unfold j2VArr
  interval_cases j
  · exact rVK (k := 0) (by norm_num) 1
  · exact rVK (k := 0) (by norm_num) 2
  · exact rVK (k := 1) (by norm_num) 1
  · exact rVK (k := 1) (by norm_num) 2
  · exact rVK (k := 2) (by norm_num) 1
  · exact rVK (k := 2) (by norm_num) 2

theorem rProd : ∀ w : List ℕ, (∀ j ∈ w, j < 6) → R (j2VProd w) (prodVG w)
  | [], _ => by
    rw [j2VProd]
    exact R.id
  | j :: w, h => by
    rw [j2VProd]
    exact (rJV (h j List.mem_cons_self)).comp (rProd w fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem k232402a : Nat.beq (prodVG j2VWordA) (J2C3.AB 0) = true := by quickRfl

theorem k232402b : Nat.beq (prodVG j2VWordB) (J2C3.AB 1) = true := by quickRfl

theorem j2VGenCheck_K : j2VGenCheck = true := by
  have hw : ∀ j ∈ j2VWordA ++ j2VWordB, j < 6 := by decide
  unfold j2VGenCheck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨hw, ?_⟩, ?_⟩
  · rw [(rProd _ fun j hj => hw j (List.mem_append_left _ hj)).eq (rAB (k := 0) (by norm_num))]
    exact k232402a
  · rw [(rProd _ fun j hj => hw j (List.mem_append_right _ hj)).eq (rAB (k := 1) (by norm_num))]
    exact k232402b

end CertificateChecks.KernelMisc.J2Fam

end
