module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs
import Certificates.Kernel.SmallSpor.M12Checks
import Certificates.Kernel.SporSch.Mathieu.M12Facts
import CFSG.Certificates.Kernel.ListBridge.TreeSound
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12

namespace CertificateChecks.KernelSmallSpor.M12

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ClassicalInvolution
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.ListBridge
open CFSG.ClassicalInvolution.ListBridge

theorem getD_map_lt {α β : Type*} [Inhabited β] (ws : List α) (f : α → β) (d : α) (b : β)
    {j : Nat} (hj : j < ws.length) : (ws.map f).getD j b = f (ws.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem k1_eq : m12KGens1 = m12CentWords1.map (evalCodes [m12gA, m12gB]) := by
  simp only [m12KGens1, tabWords, tab_eq]

theorem k2_eq : m12KGens2 = m12CentWords2.map (evalCodes [m12gA, m12gB]) := by
  simp only [m12KGens2, tabWords, tab_eq]

theorem u1_eq : m12UGens1 = u1Words.map (evalCodes m12KGens1) := by
  simp only [m12UGens1, tabWords, tab_eq, u1Words]

theorem n2_eq : m12NGens2 = n2Words.map (evalCodes m12KGens2) := by
  simp only [m12NGens2, tabWords, tab_eq, n2Words]

theorem lenK1 : m12KGens1.length = EK1.ng := by
  rw [Nat.eq_of_beq_eq_true nums.1, k1_eq, List.length_map]
  rfl

theorem lenU1 : m12UGens1.length = EU1.ng := by
  rw [Nat.eq_of_beq_eq_true nums.2.1, u1_eq, List.length_map]
  rfl

theorem lenK2 : m12KGens2.length = EK2.ng := by
  rw [Nat.eq_of_beq_eq_true nums.2.2.1, k2_eq, List.length_map]
  rfl

theorem lenN2 : m12NGens2.length = EN2.ng := by
  rw [Nat.eq_of_beq_eq_true nums.2.2.2, n2_eq, List.length_map]
  rfl

theorem prepK1 : ∀ j < EK1.ng, PRep 12 4 (EK1.G j) (m12KGens1.getD j 1) := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec bindK1 j (by rwa [← Nat.eq_of_beq_eq_true nums.1]))]
  rw [k1_eq]
  have hj' : j < (m12CentWords1.map (evalCodes [m12gA, m12gB])).length := by
    rw [← k1_eq, lenK1]
    exact hj
  exact CFSG.KS.SporSch.MOC.prep_of_imageList (KernelSporSch.M12OC.chainC1.2.2.2.1 j hj')

theorem prepK2 : ∀ j < EK2.ng, PRep 12 4 (EK2.G j) (m12KGens2.getD j 1) := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec bindK2 j (by rwa [← Nat.eq_of_beq_eq_true nums.2.2.1]))]
  rw [k2_eq]
  have hj' : j < (m12CentWords2.map (evalCodes [m12gA, m12gB])).length := by
    rw [← k2_eq, lenK2]
    exact hj
  exact CFSG.KS.SporSch.MOC.prep_of_imageList (KernelSporSch.M12OC.chainC2.2.2.2.1 j hj')

theorem prepU1 : ∀ j < EU1.ng, PRep 12 4 (EU1.G j) (m12UGens1.getD j 1) := by
  intro j hj
  have hj5 : j < 5 := by rwa [← Nat.eq_of_beq_eq_true nums.2.1]
  rw [Nat.eq_of_beq_eq_true (allN_spec bindU1 j hj5), u1_eq,
    getD_map_lt _ _ [] 1 (by change j < 5; exact hj5)]
  refine prep_pwordK (ng := 4) (by norm_num) (by norm_num) (fun k hk => ?_) _
    (allN_spec posU1 j hj5)
  exact prepK1 k (by rwa [Nat.eq_of_beq_eq_true nums.1])

theorem prepN2 : ∀ j < EN2.ng, PRep 12 4 (EN2.G j) (m12NGens2.getD j 1) := by
  intro j hj
  have hj2 : j < 2 := by rwa [← Nat.eq_of_beq_eq_true nums.2.2.2]
  rw [Nat.eq_of_beq_eq_true (allN_spec bindN2 j hj2), n2_eq,
    getD_map_lt _ _ [] 1 (by change j < 2; exact hj2)]
  refine prep_pwordK (ng := 3) (by norm_num) (by norm_num) (fun k hk => ?_) _
    (allN_spec posN2 j hj2)
  exact prepK2 k (by rwa [Nat.eq_of_beq_eq_true nums.2.2.1])

theorem mem_K1 (g : Equiv.Perm (Fin 12)) :
    g ∈ enumerationTab m12CentQ1 ↔ g ∈ Subgroup.closure {s | s ∈ m12KGens1} := by
  rw [mem_enumerationTab_iff m12CentQ1 KernelSporSch.M12OC.cent1.1, m12CentQ1,
    certificate_originalSubgroup, k1_eq]

theorem mem_K2 (g : Equiv.Perm (Fin 12)) :
    g ∈ enumerationTab m12CentQ2 ↔ g ∈ Subgroup.closure {s | s ∈ m12KGens2} := by
  rw [mem_enumerationTab_iff m12CentQ2 KernelSporSch.M12OC.cent2.1, m12CentQ2,
    certificate_originalSubgroup, k2_eq]

theorem u1_le (u : Equiv.Perm (Fin 12)) (hu : u ∈ m12UGens1) :
    u ∈ Subgroup.closure {s | s ∈ m12KGens1} := by
  rw [u1_eq, List.mem_map] at hu
  obtain ⟨wd, -, rfl⟩ := hu
  exact evalCodes_mem _ _ (fun s hs => Subgroup.subset_closure hs) wd

theorem n2_le (u : Equiv.Perm (Fin 12)) (hu : u ∈ m12NGens2) :
    u ∈ Subgroup.closure {s | s ∈ m12KGens2} := by
  rw [n2_eq, List.mem_map] at hu
  obtain ⟨wd, -, rfl⟩ := hu
  exact evalCodes_mem _ _ (fun s hs => Subgroup.subset_closure hs) wd

public theorem check9311a :
    twoConstrainedCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true :=
  twoConstrainedCheck_of_K mem_K1 (mem_permClosureList_of_K EU1.ok lenU1 prepU1 depthU1) EK1.ok
    lenK1 prepK1 EU1.ok lenU1 prepU1 u1_le powU1 normU1 selfU1

public theorem check9311b :
    indexTwoCheck m12Rep2 (enumerationTab m12CentQ2) (permClosureList m12NGens2 20) = true :=
  indexTwoCheck_of_K mem_K2 (enumerationTab_nodup m12CentQ2 KernelSporSch.M12OC.cent2.1) EK2.ok
    lenK2 prepK2 EN2.ok lenN2 prepN2 depthN2 n2_le card2
    (CFSG.KS.SporSch.MOC.prep_of_imageList KernelSporSch.M12OC.imgRep1) canonR outR

end CertificateChecks.KernelSmallSpor.M12
