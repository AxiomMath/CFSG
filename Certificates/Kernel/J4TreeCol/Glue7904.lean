module

public import Certificates.Kernel.J4TreeCol.Glue
public import Certificates.Kernel.J4TreeCol.C7904
public import Certificates.Kernel.J4TreeCol.Q7904
public import CFSG.Certificates.Kernel.J4TreeCol.UnionSound
public import Certificates.Data.CFSGNative.J4Tree.VerdictData
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColNode
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4TreeN CFSG.Sporadic.J4 CFSG.ASVolI

set_option maxRecDepth 400000

theorem ids7904 :
    ((List.range 2).map (fun j => ((rec7904 j).k,
      CFSG.KC.J4TreeCol.bitsOf (rec7904 j).om (2 ^ (CFSG.J4Tree.Native.treeWv (rec7904 j).k).length)))
      == CFSG.J4Tree.Native.Col.colUnionNodes.map fun d => (d.k, d.o)) = true := by
  quickRfl

section Union


theorem c7904 : ∀ d ∈ CFSG.J4Tree.Native.Col.colUnionNodes,
    Subgroup.normalizer (burnsideJ4NP_Wv d.k : Set J) ≤
      Subgroup.normalizer ((Subgroup.closure (burnsideJ4NP_colO d) : Subgroup J) : Set J) := by
  have hrec : ∀ j < 2, colUnionOK tabs (rec7904 j) = true := by
    intro j hj
    interval_cases j
    · exact j4colu7904_0
    · exact j4colu7904_1
  intro d hd
  have hm : (d.k, d.o) ∈ CFSG.J4Tree.Native.Col.colUnionNodes.map fun d => (d.k, d.o) :=
    List.mem_map_of_mem hd
  rw [← beq_iff_eq.1 ids7904] at hm
  obtain ⟨j, hj, hjd⟩ := List.mem_map.1 hm
  have hj' := List.mem_range.1 hj
  obtain ⟨h1, h2⟩ := Prod.mk.inj hjd
  unfold burnsideJ4NP_colO
  rw [← h1, ← h2]
  exact colUnion_sound colMats_ok tabs_ok sx_ok (hrec j hj')
    (fun hm _ _ hab hb => pairs_sound j4colcov7904 j4colq7904_all hj' hm hab hb)

end Union

end CFSG.KC.J4TreeCol

end
