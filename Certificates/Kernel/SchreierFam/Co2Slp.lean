module

public import Certificates.Kernel.SporSch.Co2M.Ker
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2SlpCheck

public section

namespace CertificateChecks.KernelSchreierFam.Co2Slp

open CFSG.KS.MatRep CertificateChecks.KernelSporSch.Co2M CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.KS.Co2M CFSG.Sporadic.Co2Cert

@[expose] noncomputable def slpM (E T : List (ℕ × ℕ)) (k : ℕ) (ds : List (List ℤ))
    (eqs nes : List (List ℤ × List ℤ)) : Bool :=
  extWordsOK k ds && extOK T.length ds &&
    (eqs.all fun e => lettersOK E.length e.1 && lettersOK E.length e.2 &&
      Nat.beq (md (wP E e.1).1) (md (wP E e.2).1)) &&
    (nes.all fun e => lettersOK E.length e.1 && lettersOK E.length e.2 &&
      !Nat.beq (md (wP E e.1).1) (md (wP E e.2).1))

@[expose] noncomputable def slpT2 (E T : List (ℕ × ℕ)) (k : ℕ) (ds : List (List ℤ))
    (w0 w1 : List ℤ) : Bool :=
  extWordsOK k ds && extOK T.length ds &&
    lettersOK E.length w0 && Nat.beq (md (wP E w0).1) (md (aT.getD 0 (0, 0)).1) &&
    lettersOK E.length w1 && Nat.beq (md (wP E w1).1) (md (aT.getD 1 (0, 0)).1)

@[expose] noncomputable def selT (T : List (ℕ × ℕ)) (idx : List ℕ) : List (ℕ × ℕ) :=
  idx.map fun i => T.getD (i - 1) (0, 0)

@[expose] noncomputable def treeOK (E T : List (ℕ × ℕ)) (ds : List (List ℤ)) : Bool :=
  Nat.beq E.length (T.length + ds.length) && decide (E.take T.length = T) &&
    (List.range ds.length).all fun j =>
      decide (E.getD (T.length + j) (0, 0) = wP (E.take (T.length + j)) (ds.getD j []))

theorem extP_take {E : List (ℕ × ℕ)} : ∀ (ds : List (List ℤ)) (T : List (ℕ × ℕ)),
    E.take T.length = T →
    (∀ j < ds.length, E.getD (T.length + j) (0, 0) = wP (E.take (T.length + j)) (ds.getD j [])) →
    T.length + ds.length ≤ E.length → extP mmK I22 T ds = E.take (T.length + ds.length)
  | [], T, hT, _, _ => by simp [extP, hT]
  | w :: ds, T, hT, hj, hl => by
    have h0 := hj 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero, hT] at h0
    have hlt : T.length < E.length := by simp at hl; omega
    have hT' : E.take (T ++ [wP T w]).length = T ++ [wP T w] := by
      rw [List.length_append, List.length_singleton, List.take_succ, hT,
        List.getElem?_eq_getElem hlt]
      rw [List.getD_eq_getElem _ _ hlt] at h0
      simp [h0]
    have ih := extP_take ds (T ++ [wP T w]) hT' (fun j hj' => by
      have := hj (j + 1) (by simp; omega)
      simp only [List.length_append, List.length_singleton, List.getD_cons_succ] at this ⊢
      rwa [show T.length + 1 + j = T.length + (j + 1) by omega])
      (by simp at hl ⊢; omega)
    have e : extP mmK I22 T (w :: ds) = extP mmK I22 (T ++ [wP T w]) ds := by
      simp only [extP, List.foldl_cons, wP]
    rw [e, ih]
    congr 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem extP_eq_of_treeOK {E T : List (ℕ × ℕ)} {ds : List (List ℤ)} (h : treeOK E T ds = true) :
    extP mmK I22 T ds = E := by
  unfold treeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hl, hT⟩, hj⟩ := h
  have hl' := Nat.eq_of_beq_eq_true hl
  rw [extP_take ds T hT hj (by omega), ← hl', List.take_length]

theorem repT_two {a b : Array ℕ} {p q : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (hb : Rep 22 co2PackedVecs b q.1 q.2) : RepT 22 co2PackedVecs #[a, b] [p, q] := by
  refine ⟨rfl, fun k hk => ?_⟩
  rcases (by simp at hk; omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact ha
  · exact hb

theorem repT_three {a b c : Array ℕ} {p q r : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (hb : Rep 22 co2PackedVecs b q.1 q.2) (hc : Rep 22 co2PackedVecs c r.1 r.2) :
    RepT 22 co2PackedVecs #[a, b, c] [p, q, r] := by
  refine ⟨rfl, fun k hk => ?_⟩
  rcases (by simp at hk; omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem rawInvs_push (A : Array (Array ℕ)) (a : Array ℕ) :
    rawInvs 2300 (A.push a) = (rawInvs 2300 A).push (invCand 2300 a) := by
  simp [rawInvs, Array.map_push]

theorem slpGo_eq : ∀ (ds : List (List ℤ)) (A : Array (Array ℕ)),
    slpGo A (rawInvs 2300 A) ds = extendArrs A ds
  | [], A => by simp [slpGo, extendArrs]
  | w :: ds, A => by
    rw [slpGo, ← rawInvs_push, slpGo_eq ds]
    simp only [extendArrs, List.foldl_cons, wordArr]

theorem slpFinal_eq (B : Array (Array ℕ)) (ds : List (List ℤ)) :
    slpFinal B ds = extendArrs B ds :=
  slpGo_eq ds B

theorem rep_wd {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT 22 co2PackedVecs A T)
    {w : List ℤ} (hw : lettersOK T.length w = true) :
    Rep 22 co2PackedVecs (wordA 2300 A (rawInvs 2300 A) w) (wP T w).1 (wP T w).2 := by
  have h := rep_word good mmK_eq I22_eq hT hw
  rw [V_size] at h
  exact h

theorem slpOK_of {B : Array (Array ℕ)} {E T : List (ℕ × ℕ)} (hB : RepT 22 co2PackedVecs B T)
    {ds : List (List ℤ)} {eqs nes : List (List ℤ × List ℤ)} (hEq : extP mmK I22 T ds = E)
    (h : slpM E T B.size ds eqs nes = true) : slpOK B ds eqs nes = true := by
  subst hEq
  unfold slpM at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hx, he⟩, hq⟩, hn⟩ := h
  have hE := repT_extend good V_size mmK_eq I22_eq ds hB he
  have hs : (extendArrs B ds).size = (extP mmK I22 T ds).length := hE.1
  unfold slpOK
  rw [slpFinal_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, hs]
  refine ⟨hx, ⟨allInv_of hE, fun e he' => ?_⟩, fun e he' => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hq e he'
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [eqA_rep (rep_wd hE h1) (rep_wd hE h2)]
    exact h3
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hn e he'
    refine ⟨⟨h1, h2⟩, ?_⟩
    rw [eqA_rep (rep_wd hE h1) (rep_wd hE h2)]
    simpa using h3

theorem slpTargets2_of {B : Array (Array ℕ)} {E T : List (ℕ × ℕ)}
    (hB : RepT 22 co2PackedVecs B T) {ds : List (List ℤ)} {w0 w1 : List ℤ}
    (hEq : extP mmK I22 T ds = E) (h : slpT2 E T B.size ds w0 w1 = true) :
    slpTargets B ds [(w0, aArrs[0]!), (w1, aArrs[1]!)] = true := by
  subst hEq
  unfold slpT2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hx, he⟩, h0⟩, h0'⟩, h1⟩, h1'⟩ := h
  have hE := repT_extend good V_size mmK_eq I22_eq ds hB he
  have hs : (extendArrs B ds).size = (extP mmK I22 T ds).length := hE.1
  unfold slpTargets
  rw [slpFinal_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, hs, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨hx, allInv_of hE, fun e he' => ?_⟩
  rcases he' with rfl | rfl
  · exact ⟨h0, by rw [eqA_rep (rep_wd hE h0) (aRep.2 0 (by decide))]; exact h0'⟩
  · exact ⟨h1, by rw [eqA_rep (rep_wd hE h1) (aRep.2 1 (by decide))]; exact h1'⟩

theorem repT_sel {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hA : RepT 22 co2PackedVecs A T)
    {idx : List ℕ} (hi : idx.all (fun i => Nat.blt (i - 1) T.length) = true) :
    RepT 22 co2PackedVecs (selArr A idx) (selT T idx) := by
  refine ⟨by simp [selArr, selT], fun k hk => ?_⟩
  simp only [selT, List.length_map] at hk
  have hik := List.all_eq_true.1 hi _ (List.getElem_mem hk)
  rw [Nat.blt_eq] at hik
  have e1 : (selArr A idx)[k]! = A[idx[k] - 1]! := by
    rw [getElem!_pos _ k (by simp [selArr, hk])]
    simp [selArr]
  have e2 : (selT T idx).getD k (0, 0) = T.getD (idx[k] - 1) (0, 0) := by
    rw [List.getD_eq_getElem _ _ (by simp [selT, hk])]
    simp [selT]
  rw [e1, e2]
  exact hA.2 _ hik

end CertificateChecks.KernelSchreierFam.Co2Slp

end
