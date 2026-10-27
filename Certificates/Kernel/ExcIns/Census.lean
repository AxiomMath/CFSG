
module

public import Certificates.Kernel.ExcIns.All
public import CFSG.Certificates.Kernel.ExcIns.OrbitList

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

theorem imgW_eq_foldr (w : List (Root m)) (c : ℕ) :
    imgW T m w c = w.foldr (fun u acc => Chk.imgN T (nroots m) u.val acc) c := by
  induction w with
  | nil => rfl
  | cons u w ih => exact congrArg (Chk.imgN T (nroots m) u.val) ih

theorem seed_of_foldr {G : Root m → Prop} {ι : Type} {R : ι → ℕ}
    (h : ∀ i : Root m, ∃ y, ∃ w : List (Root m), (∀ u ∈ w, G u) ∧
      Chk.growC T (dim m) (nroots m) (1 <<< i.val) =
      w.foldr (fun u acc => Chk.imgN T (nroots m) u.val acc) (R y)) :
    ∀ i : Root m, ∃ x w, (∀ u ∈ w, G u) ∧
      Chk.growC T (dim m) (nroots m) (1 <<< i.val) = imgW T m w (R x) := by
  simpa only [imgW_eq_foldr] using h

theorem grow_of_foldr {G : Root m → Prop} {ι : Type} {R : ι → ℕ}
    (h : ∀ x, ∀ j : Root m, (R x).testBit j.val = false → T.adj[j.val]! &&& R x ≠ 0 →
      ∃ y, ∃ w : List (Root m), (∀ u ∈ w, G u) ∧
        Chk.growC T (dim m) (nroots m) (R x ||| 1 <<< j.val) = w.foldr (fun u acc => Chk.imgN T (nroots m) u.val acc) (R y)) :
    ∀ x, ∀ j : Root m, (R x).testBit j.val = false → T.adj[j.val]! &&& R x ≠ 0 →
      ∃ y w, (∀ u ∈ w, G u) ∧
        Chk.growC T (dim m) (nroots m) (R x ||| 1 <<< j.val) = imgW T m w (R y) := by
  simpa only [imgW_eq_foldr] using h

theorem insideCensus0 : InsideCensus 0 :=
  insideCensus_of_orbits tabsOK0 (G := fun u => u.val < 4) (R := R0) pairSigned0 hR0
    (seed_of_foldr hSeed0) (grow_of_foldr hGrow0) (fun _ => False) (fun _ _ _ h => h) (fun _ h => h.elim) (fun x => Or.inl (repT0 x))

theorem insideCensus2 : InsideCensus 2 :=
  insideCensus_of_orbits tabsOK2 (G := fun u => u.val < 6) (R := R2) pairSigned2 hR2
    (seed_of_foldr hSeed2) (grow_of_foldr hGrow2) (fun _ => False) (fun _ _ _ h => h) (fun _ h => h.elim) (fun x => Or.inl (repT2 x))

theorem insideCensus3 : InsideCensus 3 :=
  insideCensus_of_orbits tabsOK3 (G := fun u => u.val < 6) (R := R3) pairSigned3 hR3
    (seed_of_foldr hSeed3) (grow_of_foldr hGrow3) (fun _ => False) (fun _ _ _ h => h) (fun _ h => h.elim) (fun x => Or.inl (repT3 x))

theorem insideCensus4 : InsideCensus 4 :=
  insideCensus_of_orbits tabsOK4 (G := fun u => u.val < 7) (R := R4) pairSigned4 hR4
    (seed_of_foldr hSeed4) (grow_of_foldr hGrow4) (fun _ => False) (fun _ _ _ h => h) (fun _ h => h.elim) (fun x => Or.inl (repT4 x))

theorem insideCensus5 : InsideCensus 5 :=
  insideCensus_of_orbits tabsOK5 (G := fun u => u.val < 8) (R := R5) pairSigned5 hR5
    (seed_of_foldr hSeed5) (grow_of_foldr hGrow5) A8 a8_closed a8_flag repT5

end CFSG.ExcInsK
