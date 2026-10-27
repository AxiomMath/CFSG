module

public import Certificates.Kernel.Sporadic.He.Order2112
public import CFSG.Sporadic.HeldB.HeBlocks

public section

namespace CertificateChecks.KernelSporSch.PHeBlocks

open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CertificateChecks.KernelSpor

theorem foldl_push_size {α β : Type} (f : α → β) :
    ∀ (l : List α) (acc : Array β),
      (l.foldl (fun acc r => acc.push (f r)) acc).size = acc.size + l.length
  | [], acc => by simp
  | r :: l, acc => by
    simp only [List.foldl_cons]
    rw [foldl_push_size f l, Array.size_push, List.length_cons]
    omega

theorem foldl_block_size {α β γ : Type} (R : List γ) (f : α → γ → β) :
    ∀ (l : List α) (acc : Array β),
      (l.foldl (fun acc t => R.foldl (fun acc r => acc.push (f t r)) acc) acc).size =
        acc.size + l.length * R.length
  | [], acc => by simp
  | t :: l, acc => by
    simp only [List.foldl_cons]
    rw [foldl_block_size R f l, foldl_push_size, List.length_cons, Nat.succ_mul]
    omega

theorem blockOf_size (n : Nat) : ∀ Ls : List (Array (Array Nat)),
    (blockOf n Ls).size = (Ls.map Array.size).prod
  | [] => by simp [blockOf]
  | L :: Ls => by
    simp only [blockOf, List.map_cons, List.prod_cons, ← blockOf_size n Ls, ← Array.foldl_toList]
    rw [foldl_block_size, Array.size_empty, Nat.zero_add, Array.length_toList,
      Array.length_toList]

theorem levelArr_size {L : Array Level} {s : List Nat}
    (hL : L.toList.map (fun l => l.pts.size) = s) (i : Nat) (hi : i < L.size) :
    (levelArr L i).size = s[i]! := by
  subst hL
  have hi' : i < (L.toList.map fun l => l.pts.size).length := by simpa using hi
  rw [levelArr, Array.size_ofFn, getElem!_pos (L.toList.map fun l => l.pts.size) i hi',
    List.getElem_map, Array.getElem_toList, getElem!_pos L i hi]

theorem block_sizes_of {L : Array Level}
    (hL : L.toList.map (fun l => l.pts.size) = [8330, 4480, 3, 18, 2]) :
    (blocksOf 8330 L heGroups).map Array.size = [8330, 4480, 108] := by
  have h5 : L.size = 5 := by
    have h := congrArg List.length hL
    simpa using h
  simp only [blocksOf, heGroups, List.map_cons, List.map_nil, blockOf_size]
  rw [levelArr_size hL 0 (by omega), levelArr_size hL 1 (by omega),
    levelArr_size hL 2 (by omega), levelArr_size hL 3 (by omega), levelArr_size hL 4 (by omega)]
  rfl

theorem block_sizes : heBlocks.map Array.size = [8330, 4480, 108] :=
  block_sizes_of (L := rawLevels 8330 heStrongArrs heBase.toArray) He2112.orbits

end CertificateChecks.KernelSporSch.PHeBlocks

end
