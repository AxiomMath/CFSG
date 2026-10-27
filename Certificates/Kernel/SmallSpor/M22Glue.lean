module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22Inputs
public import Certificates.Kernel.SmallSpor.M22Checks
import Certificates.Kernel.SporSch.Mathieu.M22Facts
public import CFSG.Certificates.Kernel.ListBridge.TreeSound

namespace CertificateChecks.KernelSmallSpor.M22

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ClassicalInvolution
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.ListBridge
open CFSG.ClassicalInvolution.ListBridge

theorem getD_map_lt {α β : Type*} [Inhabited β] (ws : List α) (f : α → β) (d : α) (b : β)
    {j : Nat} (hj : j < ws.length) : (ws.map f).getD j b = f (ws.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem kGens_eq : m22KGens1 = m22CentWords1.map (evalCodes [m22gA, m22gB]) := by
  simp only [m22KGens1, tabWords, tab_eq]

theorem uGens_eq : m22UGens1 = uWords.map (evalCodes m22KGens1) := by
  simp only [m22UGens1, tabWords, tab_eq, uWords]

public theorem lenK : m22KGens1.length = EK.ng := by
  rw [Nat.eq_of_beq_eq_true nums.1, kGens_eq, List.length_map]
  rfl

public theorem lenU : m22UGens1.length = EU.ng := by
  rw [Nat.eq_of_beq_eq_true nums.2, uGens_eq, List.length_map]
  rfl

public theorem prepK : ∀ j < EK.ng, PRep 22 5 (EK.G j) (m22KGens1.getD j 1) := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec bindK j (by rwa [← Nat.eq_of_beq_eq_true nums.1]))]
  rw [kGens_eq]
  have hj' : j < (m22CentWords1.map (evalCodes [m22gA, m22gB])).length := by
    rw [← kGens_eq, lenK]
    exact hj
  exact CFSG.KS.SporSch.MOC.prep_of_imageList (KernelSporSch.M22OC.chainC1.2.2.2.1 j hj')

public theorem prepU : ∀ j < EU.ng, PRep 22 5 (EU.G j) (m22UGens1.getD j 1) := by
  intro j hj
  have hj3 : j < 3 := by rwa [← Nat.eq_of_beq_eq_true nums.2]
  rw [Nat.eq_of_beq_eq_true (allN_spec bindU j hj3), uGens_eq,
    getD_map_lt _ _ [] 1 (by change j < 3; exact hj3)]
  refine prep_pwordK (ng := 3) (by norm_num) (by norm_num) (fun k hk => ?_) _
    (allN_spec posU j hj3)
  exact prepK k (by rwa [Nat.eq_of_beq_eq_true nums.1])

public theorem mem_K (g : Equiv.Perm (Fin 22)) :
    g ∈ enumerationTab m22CentQ1 ↔ g ∈ Subgroup.closure {s | s ∈ m22KGens1} := by
  rw [mem_enumerationTab_iff m22CentQ1 KernelSporSch.M22OC.cent1.1, m22CentQ1,
    certificate_originalSubgroup, kGens_eq]

public theorem mem_U (u : Equiv.Perm (Fin 22)) :
    u ∈ permClosureList m22UGens1 20 ↔ u ∈ Subgroup.closure {s | s ∈ m22UGens1} :=
  mem_permClosureList_of_K EU.ok lenU prepU depth u

theorem uGens_le (u : Equiv.Perm (Fin 22)) (hu : u ∈ m22UGens1) :
    u ∈ Subgroup.closure {s | s ∈ m22KGens1} := by
  rw [uGens_eq, List.mem_map] at hu
  obtain ⟨wd, -, rfl⟩ := hu
  exact evalCodes_mem _ _ (fun s hs => Subgroup.subset_closure hs) wd

public theorem check9312 :
    twoConstrainedCheck (enumerationTab m22CentQ1) (permClosureList m22UGens1 20) 6 = true :=
  twoConstrainedCheck_of_K mem_K mem_U EK.ok lenK prepK EU.ok lenU prepU uGens_le pow norm self

end CertificateChecks.KernelSmallSpor.M22
