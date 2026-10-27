module

public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs

public section

namespace CertificateChecks.KernelLC.Fi24B

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

theorem size_compA (n : Nat) (t u : Array Nat) : (compA n t u).size = n := by simp [compA]

theorem eq_of_rep {n : Nat} {a b : Array Nat} {g : Equiv.Perm (Fin n)} (ha : a.size = n)
    (hb : b.size = n) (hra : Rep n a g) (hrb : Rep n b g) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro i h1 h2
  have hi : i < n := by omega
  rw [← getElem!_pos a i h1, ← getElem!_pos b i h2, hra.apply hi, hrb.apply hi]

theorem rep_invCand_of {n : Nat} {a : Array Nat} {g : Equiv.Perm (Fin n)} (h : Rep n a g) :
    Rep n (invCand n a) g⁻¹ := by
  have hv := CFSG.RankThree.Native.F2.validA_of_rep h
  have e := Rep.unique (CFSG.RankThree.Native.rep_of_validA hv) h
  have h2 := CFSG.RankThree.Native.rep_inv_of_validA hv
  rwa [e] at h2

theorem rep_conjA {n : Nat} {a x : Array Nat} {g X : Equiv.Perm (Fin n)} (ha : Rep n a g)
    (hx : Rep n x X) : Rep n (conjA n a x) (g * (X * g⁻¹)) :=
  rep_compA ha (rep_compA hx (rep_invCand_of ha))

theorem conjA_compA {n : Nat} {s e x : Array Nat} {S E X : Equiv.Perm (Fin n)} (hs : Rep n s S)
    (he : Rep n e E) (hx : Rep n x X) : conjA n (compA n s e) x = conjA n s (conjA n e x) := by
  refine eq_of_rep (size_compA _ _ _) (size_compA _ _ _) (rep_conjA (rep_compA hs he) hx) ?_
  have h := rep_conjA hs (rep_conjA he hx)
  have e2 : S * (E * (X * E⁻¹) * S⁻¹) = S * E * (X * (S * E)⁻¹) := by group
  rw [e2] at h
  exact h

theorem conjs_foldl {n r : Nat} {gens : Array (Array Nat)} {rep : Array Nat} (hr : 0 < r)
    (hg : ∀ k < r, ∃ g, Rep n gens[k]! g) (hrep : ∃ R, Rep n rep R) :
    ∀ (L : List Nat) (A : Array (Array Nat)), (∀ j < A.size, ∃ e, Rep n A[j]! e) →
      (∀ i < L.length, L[i]! / r < A.size + i) →
      (L.foldl (fun acc t => acc.push (compA n gens[t % r]! acc[t / r]!)) A).map
          (fun g => conjA n g rep) =
        L.foldl (fun acc t => acc.push (conjA n gens[t % r]! acc[t / r]!))
          (A.map fun g => conjA n g rep)
  | [], _, _, _ => rfl
  | t :: L, A, hA, hL => by
    rw [List.foldl_cons, List.foldl_cons]
    have ht : t / r < A.size := by
      have := hL 0 (by simp)
      simpa using this
    obtain ⟨S, hS⟩ := hg (t % r) (Nat.mod_lt _ hr)
    obtain ⟨E, hE⟩ := hA (t / r) ht
    obtain ⟨R, hR⟩ := hrep
    have hmap : (A.map fun g => conjA n g rep).push (conjA n gens[t % r]!
        (A.map fun g => conjA n g rep)[t / r]!) =
        (A.push (compA n gens[t % r]! A[t / r]!)).map fun g => conjA n g rep := by
      rw [Array.map_push, getElem!_pos _ (t / r) (by simpa using ht), Array.getElem_map,
        ← getElem!_pos A (t / r) ht, conjA_compA hS hE hR]
    rw [hmap]
    refine conjs_foldl hr hg ⟨R, hR⟩ L _ (fun j hj => ?_) (fun i hi => ?_)
    · rw [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [getElem!_pos _ j (by simp; omega), Array.getElem_push_lt hj, ← getElem!_pos A j hj]
        exact hA j hj
      · rw [getElem!_pos _ A.size (by simp), Array.getElem_push_eq]
        exact ⟨S * E, rep_compA hS hE⟩
    · have := hL (i + 1) (by simp; omega)
      rw [Array.size_push]
      simp only [List.getElem!_cons_succ] at this
      omega

theorem conjs_eq {n r : Nat} {gens : Array (Array Nat)} {rep : Array Nat} {tree : Array Nat}
    (hr : 0 < r) (hg : ∀ k < r, ∃ g, Rep n gens[k]! g) (hrep : ∃ R, Rep n rep R)
    (hsz : rep.size = n) (ht : ∀ i < tree.size, tree[i]! / r < i + 1) :
    (tree.foldl (fun acc t => acc.push (compA n gens[t % r]! acc[t / r]!)) #[idA n]).map
        (fun g => conjA n g rep) = treeConjN n r gens rep tree := by
  obtain ⟨R, hR⟩ := hrep
  have hid : (#[idA n].map fun g => conjA n g rep) = #[rep] := by
    have hc : conjA n (idA n) rep = rep := by
      have h1 := rep_conjA (rep_idA (n := n)) hR
      rw [one_mul, inv_one, mul_one] at h1
      exact eq_of_rep (size_compA _ _ _) hsz h1 hR
    simp [hc]
  rw [treeConjN, ← Array.foldl_toList, ← Array.foldl_toList,
    conjs_foldl hr hg ⟨R, hR⟩ tree.toList #[idA n] (fun j hj => ⟨1, by
      have : j = 0 := by simpa using hj
      subst this
      exact rep_idA⟩) (fun i hi => by
      have hi' : i < tree.size := by simpa using hi
      have h1 := ht i hi'
      have e : tree.toList[i]! = tree[i]! := by
        rw [getElem!_pos _ i hi, getElem!_pos tree i hi', Array.getElem_toList]
      have e1 : (#[idA n] : Array (Array Nat)).size = 1 := rfl
      rw [e, e1]
      omega), hid]

end CertificateChecks.KernelLC.Fi24B

end
