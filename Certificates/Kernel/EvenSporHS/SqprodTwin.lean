module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUCheck

public section

namespace CertificateChecks.EvenSporHS

open CFSG.EvenSporadicStandard.TwoHS

@[expose] def r4eq (a b : R4) : Bool :=
  a.a00 == b.a00 && a.a01 == b.a01 && a.a02 == b.a02 && a.a03 == b.a03 &&
  a.a10 == b.a10 && a.a11 == b.a11 && a.a12 == b.a12 && a.a13 == b.a13 &&
  a.a20 == b.a20 && a.a21 == b.a21 && a.a22 == b.a22 && a.a23 == b.a23 &&
  a.a30 == b.a30 && a.a31 == b.a31 && a.a32 == b.a32 && a.a33 == b.a33

theorem r4eq_iff {a b : R4} : r4eq a b = true ↔ a = b := by
  cases a
  cases b
  simp [r4eq, and_assoc]

@[expose] def nubR4 : List R4 → List R4
  | [] => []
  | x :: xs => if xs.any (r4eq x) then nubR4 xs else x :: nubR4 xs

theorem mem_nubR4 {a : R4} : ∀ {l : List R4}, a ∈ nubR4 l ↔ a ∈ l
  | [] => by simp [nubR4]
  | x :: xs => by
    have ih := @mem_nubR4 a xs
    unfold nubR4
    split
    · rename_i h
      obtain ⟨y, hy, hxy⟩ := List.any_eq_true.1 h
      have hxy' : x = y := r4eq_iff.1 hxy
      subst hxy'
      constructor
      · intro ha
        exact List.mem_cons_of_mem _ (ih.1 ha)
      · intro ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ih.2 hy
        · exact ih.2 ha
    · simp [ih]

@[expose] def sqsT : List R4 := nubR4 (q0R.map fun a => rmul a a)

@[expose] def prodsT : List R4 := sqsT.flatMap fun a => sqsT.map (rmul a)

@[expose] def sqprodTwin : Bool :=
  q0R.all fun b => prodsT.any (fun x => r4eq x b) || prodsT.any (fun x => r4eq x (rneg b))

theorem any_r4eq_iff (l : List R4) (b : R4) : l.any (fun x => r4eq x b) = true ↔ b ∈ l := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [← r4eq_iff.1 h]
    exact hx
  · intro hb
    exact ⟨b, hb, r4eq_iff.2 rfl⟩

theorem mem_nub_dedup (l : List R4) (a : R4) : a ∈ nubR4 l ↔ a ∈ l.dedup := by
  rw [mem_nubR4, List.mem_dedup]

theorem mem_prods_congr {S S' : List R4} (h : ∀ a, a ∈ S ↔ a ∈ S') (b : R4) :
    b ∈ S.flatMap (fun a => S.map (rmul a)) ↔ b ∈ S'.flatMap (fun a => S'.map (rmul a)) := by
  simp only [List.mem_flatMap, List.mem_map, h]

theorem mem_prodsT_iff (b : R4) : b ∈ prodsT ↔ b ∈ sqprodsR :=
  mem_prods_congr (mem_nub_dedup _) b

theorem contains_eq (b : R4) : sqprodsR.contains b = prodsT.any (fun x => r4eq x b) := by
  rw [Bool.eq_iff_iff, any_r4eq_iff, mem_prodsT_iff, List.contains_iff_mem]

theorem uSqprodCheck_eq_twin : uSqprodCheck = sqprodTwin := by
  have hf : (fun b => sqprodsR.contains b || sqprodsR.contains (rneg b)) =
      (fun b => prodsT.any (fun x => r4eq x b) || prodsT.any (fun x => r4eq x (rneg b))) := by
    funext b
    rw [contains_eq b, contains_eq (rneg b)]
  unfold uSqprodCheck sqprodTwin
  rw [hf]

end CertificateChecks.EvenSporHS
