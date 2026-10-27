module

public import Certificates.Kernel.Fi22Omega.Mem
public import Certificates.Kernel.Fi22Omega.Nodes0
public import Certificates.Kernel.Fi22Omega.Nodes1
public import Certificates.Kernel.Fi22Omega.Nodes2
public import Certificates.Kernel.Fi22Omega.Nodes3
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Fi22Omega.Forest
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.RankThree.Native.Fi22FiveCheckInputs
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open Equiv CFSG.KC.Fi22Omega CFSG.KC.Benes CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw
  CFSG.KC.BfsPin CertificateChecks.KernelI242 CertificateChecks.KernelSpor
  CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

#kc_forall_tree chunks_ok
  (fun c => CFSG.KC.Fi22Omega.chunkOK CertificateChecks.KernelFi22Omega.T
    CertificateChecks.KernelFi22Omega.NT CertificateChecks.KernelFi22Omega.MS c = true) 966
  CertificateChecks.KernelFi22Omega.ch1023301n

theorem nodes_ok : ∀ i < 61776, nodeOK T NT MS i = true := nodes_of_chunks chunks_ok

@[expose] noncomputable def yWord (w : List Nat) : Perm (Fin 3510) :=
  w.foldl (fun g r => i242y r * g) 1

@[expose] def hW (l : Nat) : List Nat := if l = 0 then [6, 5, 4, 5, 7, 3] else [2, 0, 5, 1, 2, 7]

@[expose] noncomputable def hGrp : Subgroup (Perm (Fin 3510)) :=
  Subgroup.closure {yWord (hW 0), yWord (hW 1)}

@[expose] noncomputable def nodeSet (i : Nat) : Set (Fin 3510) := maskSet (msk (recAt T i))

theorem y_cn {r : Nat} (hr : r < 8) : cn (Y.S r) = true :=
  (band_true (allN_spec ySift r hr)).1

theorem rep_y {r : Nat} (hr : r < 8) :
    Rep 3510 (unpack 3510 12 (Y.S r)) (i242y r) := by
  rw [← yArr_eq hr]
  exact i242_rep_y hr

theorem rep_fold : ∀ (w : List Nat), (∀ r ∈ w, r < 8) →
    ∀ (acc : Nat) (g : Perm (Fin 3510)), cn acc = true → Rep 3510 (unpack 3510 12 acc) g →
      cn (w.foldl (fun a r => pc (Y.S r) a) acc) = true ∧
      Rep 3510 (unpack 3510 12 (w.foldl (fun a r => pc (Y.S r) a) acc))
        (w.foldl (fun g r => i242y r * g) g)
  | [], _, _, _, hc, hg => ⟨hc, hg⟩
  | r :: w, hw, acc, g, hc, hg => by
    have hr : r < 8 := hw r (List.mem_cons_self ..)
    refine rep_fold w (fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')) _ _ (cn_pc (y_cn hr) hc) ?_
    rw [← compA_pc (y_cn hr) hc]
    exact rep_compA (rep_y hr) hg

theorem rep_wordK {w : List Nat} (hw : ∀ r ∈ w, r < 8) :
    Rep 3510 (unpack 3510 12 (wordK Y.S w)) (yWord w) := by
  have h := rep_fold w hw pid 1 Fi22G.cnId (by rw [← idA_eq]; exact rep_idA)
  exact h.2

theorem hW_lt {l r : Nat} (h : r ∈ hW l) : r < 8 := by
  unfold hW at h
  split at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> omega

theorem pg_of_rep {p : Nat} {σ : Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 p) σ)
    (q : Fin 3510) : pg 12 4095 p q = σ q := by
  rw [← unpack_get3510 q.2]
  exact h q

theorem bindH (l : Nat) (hl : l < 2) : bindOK NT (wordK Y.S (hW l)) l = true := by
  interval_cases l
  · exact bindH0
  · exact bindH1

theorem h_acts (l : Nat) (hl : l < 2) :
    StagesValid 12 (NT l) ∧ ∀ p : Fin 3510, benesPerm 12 (NT l) p = ((yWord (hW l))⁻¹ p : Nat) :=
  netActs_of_bind (bindH l hl) (pg_of_rep (rep_wordK fun _ h => hW_lt h))

theorem hW_mem (l : Nat) (hl : l < 2) : yWord (hW l) ∈ hGrp := by
  interval_cases l
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem node_orbit :
    ∀ i < 61776, ∃ h ∈ hGrp, nodeSet i = h • nodeSet (MS (blkF (recAt T i))) :=
  forest_orbit nodes_ok hW_mem h_acts

theorem yWord_mem {w : List Nat} (hw : ∀ r ∈ w, r < 8) : yWord w ∈ i242Y := by
  unfold yWord
  suffices h : ∀ (w : List Nat), (∀ r ∈ w, r < 8) → ∀ g ∈ i242Y,
      w.foldl (fun g r => i242y r * g) g ∈ i242Y from h w hw 1 i242Y.one_mem
  intro w
  induction w with
  | nil => exact fun _ _ hg => hg
  | cons r w ih =>
    intro hw g hg
    rw [List.foldl_cons]
    exact ih (fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')) _
      (i242Y.mul_mem (i242y_mem_Y (hw r (List.mem_cons_self ..))) hg)

theorem hGrp_le : hGrp ≤ i242Y := by
  rw [hGrp, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact yWord_mem fun _ h => hW_lt h
  · exact yWord_mem fun _ h => hW_lt h

end CertificateChecks.KernelFi22Omega

end
