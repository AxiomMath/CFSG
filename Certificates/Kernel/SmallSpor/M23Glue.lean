module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23Inputs
import Certificates.Kernel.SmallSpor.M23Checks
import Certificates.Kernel.SporSch.Mathieu.M23Facts
import CFSG.Certificates.Kernel.ListBridge.PackSound
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic

namespace CertificateChecks.KernelSmallSpor.M23

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ClassicalInvolution
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.ListBridge
open CFSG.ClassicalInvolution.ListBridge

theorem getD_map_lt {α β : Type*} [Inhabited β] (ws : List α) (f : α → β) (d : α) (b : β)
    {j : Nat} (hj : j < ws.length) : (ws.map f).getD j b = f (ws.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem kGens_eq : m23KGens1 = m23CentWords1.map (evalCodes [m23PermA, m23PermB]) := by
  simp only [m23KGens1, tabWords, tab_eq]

theorem uGens_eq : m23UGens1 = uWords.map (evalCodes m23KGens1) := by
  simp only [m23UGens1, tabWords, tab_eq, uWords]

theorem lenK : m23KGens1.length = EK.ng := by
  rw [Nat.eq_of_beq_eq_true nums.1, kGens_eq, List.length_map]
  rfl

theorem lenU : m23UGens1.length = EU.ng := by
  rw [Nat.eq_of_beq_eq_true nums.2.1, uGens_eq, List.length_map]
  rfl

theorem prepK : ∀ j < EK.ng, PRep 23 5 (EK.G j) (m23KGens1.getD j 1) := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec bindK j (by rwa [← Nat.eq_of_beq_eq_true nums.1]))]
  rw [kGens_eq]
  have hj' : j < (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).length := by
    rw [← kGens_eq, lenK]
    exact hj
  exact CFSG.KS.SporSch.MOC.prep_of_imageList (KernelSporSch.M23OC.chainC1.2.2.2.1 j hj')

theorem prepU : ∀ j < EU.ng, PRep 23 5 (EU.G j) (m23UGens1.getD j 1) := by
  intro j hj
  have hj4 : j < 4 := by rwa [← Nat.eq_of_beq_eq_true nums.2.1]
  rw [Nat.eq_of_beq_eq_true (allN_spec bindU j hj4), uGens_eq,
    getD_map_lt _ _ [] 1 (by change j < 4; exact hj4)]
  refine prep_pwordK (ng := 4) (by norm_num) (by norm_num) (fun k hk => ?_) _
    (allN_spec posU j hj4)
  exact prepK k (by rwa [Nat.eq_of_beq_eq_true nums.1])

theorem mem_K (g : Equiv.Perm (Fin 23)) :
    g ∈ enumerationTab m23CentQ1 ↔ g ∈ Subgroup.closure {s | s ∈ m23KGens1} := by
  rw [mem_enumerationTab_iff m23CentQ1 KernelSporSch.M23OC.cent1.1, m23CentQ1,
    certificate_originalSubgroup, kGens_eq]

theorem mem_U (u : Equiv.Perm (Fin 23)) :
    u ∈ permClosureList m23UGens1 20 ↔ u ∈ Subgroup.closure {s | s ∈ m23UGens1} := by
  refine mem_permClosureList_iff _ _ ?_ u
  rw [(enum_closure EU.ok lenU prepU).2, Nat.eq_of_beq_eq_true nums.2.2]
  norm_num

theorem uGens_le (u : Equiv.Perm (Fin 23)) (hu : u ∈ m23UGens1) :
    u ∈ Subgroup.closure {s | s ∈ m23KGens1} := by
  rw [uGens_eq, List.mem_map] at hu
  obtain ⟨wd, -, rfl⟩ := hu
  exact evalCodes_mem _ _ (fun s hs => Subgroup.subset_closure hs) wd

public theorem check9313 :
    twoConstrainedCheck (enumerationTab m23CentQ1) (permClosureList m23UGens1 20) 4 = true :=
  twoConstrainedCheck_of_K mem_K mem_U EK.ok lenK prepK EU.ok lenU prepU uGens_le pow norm self

end CertificateChecks.KernelSmallSpor.M23
