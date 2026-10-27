
module

public import Certificates.Kernel.SporSch.Co2M.FratMD
public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import CFSG.Sporadic.Co2Schreier.Tuples

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native

theorem rep_I22 : MatRep.Rep 22 co2PackedVecs (idA 2300) I22 I22 := by
  have h := rep_idA good
  rwa [V_size, ← I22_eq] at h

theorem rep_prodPT {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT 22 co2PackedVecs A T) :
    ∀ (l : List ℕ), (∀ i ∈ l, i < T.length) → ∀ (acc : Array ℕ) (p : ℕ × ℕ),
      MatRep.Rep 22 co2PackedVecs acc p.1 p.2 →
      MatRep.Rep 22 co2PackedVecs (l.foldl (fun acc i => compA 2300 acc A[i]!) acc)
        (l.foldl (fun acc i => cmpP acc (T.getD i (0, 0))) p).1
        (l.foldl (fun acc i => cmpP acc (T.getD i (0, 0))) p).2
  | [], _, _, _, h => h
  | i :: l, hl, acc, p, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact rep_prodPT hT l (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ _
      (rep_cmp h (repT_get hT (hl i List.mem_cons_self)))

theorem rep_prodArrM {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT 22 co2PackedVecs A T)
    {l : List ℕ} (hl : ∀ i ∈ l, i < T.length) :
    MatRep.Rep 22 co2PackedVecs (prodArr A l) (prodPT T l).1 (prodPT T l).2 :=
  rep_prodPT hT l hl _ (I22, I22) rep_I22

theorem repT_ofList {α : Type} {L : List α} {f : α → Array ℕ} {F : α → ℕ × ℕ}
    (h : ∀ a ∈ L, MatRep.Rep 22 co2PackedVecs (f a) (F a).1 (F a).2) :
    RepT 22 co2PackedVecs (L.map f).toArray (L.map F) := by
  refine ⟨by simp, fun k hk => ?_⟩
  rw [List.length_map] at hk
  rw [getElem!_pos _ k (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [List.getElem_toArray, List.getElem_map]
  exact h _ (List.getElem_mem hk)

theorem specs_lt : (fratSpecs.all fun l => l.all fun i => decide (i < 15)) = true ∧
    (yBasisSpecs.all fun l => l.all fun i => decide (i < 15)) = true ∧
    fratSpecs.length = 12 ∧ yBasisSpecs.length = 5 ∧ fratDerivs.length = 4 ∧
    extOK 12 fratDerivs = true := by
  decide +kernel

theorem fratOrigRep : RepT 22 co2PackedVecs fratOrig fratT0 := by
  refine repT_ofList fun l hl => rep_cmp (rep_prodArrM sRep ?_) (rep_prodArrM sRep ?_) <;>
  · intro i hi
    have := List.all_eq_true.1 (List.all_eq_true.1 specs_lt.1 l hl) i hi
    rw [sT_len]
    simpa using this

theorem fratT0_len : fratT0.length = 12 := by rw [fratT0, List.length_map, specs_lt.2.2.1]

theorem fratRep : RepT 22 co2PackedVecs fratStrong fratT :=
  repT_extend good V_size mmK_eq I22_eq _ fratOrigRep (by rw [fratT0_len]; exact specs_lt.2.2.2.2.2)

theorem fratT_len : fratT.length = 16 := by
  rw [← fratRep.1, fratStrong, extendArrs_size, fratOrigRep.1, fratT0_len, specs_lt.2.2.2.2.1]

theorem yBRep : RepT 22 co2PackedVecs yBasisArrs yBT :=
  repT_ofList fun l hl => rep_prodArrM sRep (by
    intro i hi
    have := List.all_eq_true.1 (List.all_eq_true.1 specs_lt.2.1 l hl) i hi
    rw [sT_len]
    simpa using this)

theorem yBT_len : yBT.length = 5 := by rw [yBT, List.length_map, specs_lt.2.2.2.1]

theorem yRep (w : ℕ) : MatRep.Rep 22 co2PackedVecs (yArr w) (yP w).1 (yP w).2 :=
  rep_prodArrM yBRep (by
    intro i hi
    rw [yBT_len]
    unfold bits5 at hi
    exact List.mem_range.1 (List.mem_filter.1 hi).1)

end CertificateChecks.KernelSporSch.Co2M

end
