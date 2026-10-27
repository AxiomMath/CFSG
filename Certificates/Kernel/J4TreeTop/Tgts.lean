module

public import Certificates.Kernel.J4TreeTop.NodeGlue
public import Certificates.Kernel.J4TreeTop.Walk2
public import Certificates.Kernel.J4TreeTop.Walk3
public import Certificates.Kernel.J4TreeTop.Walk4
public import Certificates.Kernel.J4TreeTop.Walk7
public import Certificates.Kernel.J4TreeTop.Walk107
public import Certificates.Kernel.J4TreeTop.Walk124
public import Certificates.Kernel.J4TreeTop.Walk129
public import Certificates.Kernel.J4TreeTop.Walk134

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] noncomputable def kidsTsOK (i : Nat) (d : TopNode) (ts : List Nat) : Bool :=
  (List.range d.children.length).all fun j =>
    childOK i j && (tgtOK (d.children.getD j default).target ||
      ts.contains (d.children.getD j default).target)

section Walk


theorem topTgt_walk {i k : ℕ} (hi : i < 9) (hk : (topNodes.getD i default).node = k)
    {cs : List (ℕ × ℕ)} (hcs : treeBasis k = cs) {H : WHd} {D : ℕ → List ℕ}
    (hH : whdOK tabs (cs.map (ccT tabs)) H = true)
    (hD : ∀ e < 1024, walkOK tabs (cs.map (ccT tabs)) H e (D e) = true) : TopTgt k := by
  have hg : topGlobOK tabs i (syRec i) = true := sy_all i hi
  have hk' : (syRec i).k = k := (topGlob_sound tabs_ok topHq hg).1.trans hk
  have ht := walk_topTgt tabs_ok topHq hg (H := H) (D := D) (by rw [hk', hcs]; exact hH)
    (by rw [hk', hcs]; exact hD)
  rwa [hk'] at ht

theorem topTgt2 : TopTgt 2 := topTgt_walk (i := 1) (by norm_num) rfl wC2_eq hd2_ok w2_all

theorem topTgt3 : TopTgt 3 := topTgt_walk (i := 2) (by norm_num) rfl wC3_eq hd3_ok w3_all

theorem topTgt4 : TopTgt 4 := topTgt_walk (i := 3) (by norm_num) rfl wC4_eq hd4_ok w4_all

theorem topTgt7 : TopTgt 7 := topTgt_walk (i := 4) (by norm_num) rfl wC7_eq hd7_ok w7_all

theorem topTgt107 : TopTgt 107 :=
  topTgt_walk (i := 5) (by norm_num) rfl wC107_eq hd107_ok w107_all

theorem topTgt124 : TopTgt 124 :=
  topTgt_walk (i := 6) (by norm_num) rfl wC124_eq hd124_ok w124_all

theorem topTgt129 : TopTgt 129 :=
  topTgt_walk (i := 7) (by norm_num) rfl wC129_eq hd129_ok w129_all

theorem topTgt134 : TopTgt 134 :=
  topTgt_walk (i := 8) (by norm_num) rfl wC134_eq hd134_ok w134_all

end Walk


theorem top_facts_ts {i : ℕ} (hi : i < 9) {d : TopNode} (hd : topNodes.getD i default = d)
    {ts : List ℕ} (hts : ∀ k ∈ ts, TopTgt k) (hk : kidsTsOK i d ts = true)
    (hcov : TopCover (burnsideJ4NP_Rep d.node) (d.children.map fun c => burnsideJ4NP_treeElt c.y)) :
    burnsideJ4NP_Aff2A →
    Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep d.node : Set J)) = treeOrd d.node →
      burnsideJ4NP_TreeStep d.node ∧
        ∀ kd ∈ d.kids, Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep kd.1 : Set J)) =
          treeOrd kd.1 := by
  have hk' : ∀ j < d.children.length, childOK i j = true ∧
      (tgtOK (d.children.getD j default).target = true ∨
        (d.children.getD j default).target ∈ ts) := by
    intro j hj
    have := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
    simpa only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] using this
  have hg : topGlobOK tabs i (syRec i) = true := sy_all i hi
  intro haff
  refine topNode_facts haff tabs_ok topHq hd hg (fun j hj => child_rec (hk' j hj).1)
    (fun j hj h0 => ?_) hcov
  rcases (hk' j hj).2 with h | h
  · exact topTgt_of_tgtOK h h0
  · exact hts _ h

end CFSG.KC.J4TreeT
