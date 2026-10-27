
module

public import Certificates.Kernel.J4Count.FixCBase

public import Certificates.Kernel.J4Count.FixCPair

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixC

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.KC.J4FixC CFSG.KD.J4FixC CFSG.KS.SporSch.C11 CFSG.Sporadic.GLQ
open CFSG.Sporadic.SmallF2.Native (vecMulN)
open CFSG.KC.J4Count (combo decode BS PS)
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4NoCK
open CertificateChecks.KernelSporSch.J4Eta CertificateChecks.KernelSporSch.J4NoCP

section Generic

variable {Λ : Type*} [Group Λ] [Finite Λ]

end Generic

section Words

theorem letter_inv_smul (c s : ℕ) :
    (letter x y (codeL c))⁻¹ • toRow (toVecD 112 s) =
      toRow (toVecD 112 (CFSG.KC.J4Q.vecJ CFSG.KD.J4Q.rm s (letM (R 1) (R 10) (R 2) (R 11) c))) := by
  have hx := rep_x matFacts
  have hy := rep_y matFacts
  rw [letM_eq]
  rcases c with _ | _ | _ | c
  · have e : letter x y (codeL 0) = x := by simp [letter, codeL]
    rw [e, inv_smul_toRow hx]
    change toRow (toVecD 112 (vecMulN 112 Xn.1 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4Regs.hX.1.1, J4Regs.hX.1.2]
    rfl
  · have e : letter x y (codeL 1) = x⁻¹ := by simp [letter, codeL]
    rw [e, inv_smul_toRow (rep_invP hx)]
    change toRow (toVecD 112 (vecMulN 112 Xn.2 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4Regs.hX.2.1, J4Regs.hX.2.2]
    rfl
  · have e : letter x y (codeL 2) = y := by simp [letter, codeL]
    rw [e, inv_smul_toRow hy]
    change toRow (toVecD 112 (vecMulN 112 Yn.1 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4Regs.hY.1.1, J4Regs.hY.1.2]
    rfl
  · have e : letter x y (codeL (c + 3)) = y⁻¹ := by simp [letter, codeL]
    rw [e, inv_smul_toRow (rep_invP hy), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    change toRow (toVecD 112 (vecMulN 112 Yn.2 s)) = _
    rw [CFSG.KS.SporSch.J4B.vec_enc J4Real.hK J4Regs.hY.2.1, J4Regs.hY.2.2]
    rfl

theorem walk_sound : ∀ (w : List ℕ) (s : ℕ),
    (signedWord x y (toI w))⁻¹ • toRow (toVecD 112 s) =
      toRow (toVecD 112 (walkK CFSG.KD.J4Q.rm (R 1) (R 10) (R 2) (R 11) w s))
  | [], s => by
    change (signedWord x y [])⁻¹ • _ = _
    simp [signedWord]
    rfl
  | c :: w, s => by
    have e : signedWord x y (toI (c :: w)) = letter x y (codeL c) * signedWord x y (toI w) := by
      simp [signedWord, toI]
    rw [e, mul_inv_rev, mul_smul, letter_inv_smul, walk_sound w]
    change _ = toRow (toVecD 112 (CFSG.KC.Enum.strictN _ (walkK _ _ _ _ _ w)))
    rw [sN]

theorem gsl_rep {l : ℕ} (hl : l < 7) (i : ℕ) :
    PairRep (nth 1 (gsl l) i) (nth pidP (GP l) i) ∧
      PairRep (nth 1 (gsl l) i)⁻¹ (nth pidP (GIP l) i) := by
  rw [gsl, GP, GIP, nth_eq, nth_eq, nth_eq, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_map]
  cases e : (GN l)[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, inv_one]
    exact ⟨pairRep_one, pairRep_one⟩
  | some g =>
    simp only [Option.map_some, Option.getD_some]
    have hg := List.mem_of_getElem? e
    have hb := (fixAllK_spec (CFSG.KS.allN_spec fix_ok l hl) g hg).1
    exact ⟨pairRep_gen J4X.bind J4XI.bind J4Y.bind J4YI.bind g,
      pairRep_genI J4X.bind J4XI.bind J4Y.bind J4YI.bind g hb⟩

theorem WE_rep {l : ℕ} (hl : l < 7) (w : List ℕ) : PairRep (WE l w) (EV l w) :=
  pairRep_evalW (fun i => (gsl_rep hl i).1) (fun i => (gsl_rep hl i).2) w

end Words

section Conj

theorem card_cN_conj {h : J} (hh : h ∈ H) (g : J) :
    Nat.card ↥(Subgroup.centralizer {h * g * h⁻¹} ⊓ N) =
      Nat.card ↥(Subgroup.centralizer {g} ⊓ N) := by
  have hN : ∀ u ∈ H, ∀ n ∈ N, u * n * u⁻¹ ∈ N := conj_mem_N_of_mem_H
  refine Nat.card_congr
    { toFun := fun n => ⟨h⁻¹ * n * h, ?_, ?_⟩
      invFun := fun n => ⟨h * n * h⁻¹, ?_, ?_⟩
      left_inv := fun n => Subtype.ext (by simp only; group)
      right_inv := fun n => Subtype.ext (by simp only; group) }
  · have e := Subgroup.mem_centralizer_singleton_iff.1 n.2.1
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc h⁻¹ * ↑n * h * g = h⁻¹ * (↑n * (h * g * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * g * h⁻¹) * ↑n) * h := by rw [e]
      _ = g * (h⁻¹ * ↑n * h) := by group
  · have := hN h⁻¹ (H.inv_mem hh) n n.2.2
    rwa [inv_inv] at this
  · have e := Subgroup.mem_centralizer_singleton_iff.1 n.2.1
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc h * ↑n * h⁻¹ * (h * g * h⁻¹) = h * (↑n * g) * h⁻¹ := by group
      _ = h * (g * ↑n) * h⁻¹ := by rw [e]
      _ = h * g * h⁻¹ * (h * ↑n * h⁻¹) := by group
  · exact hN h hh n n.2.2

end Conj

section Local

theorem PE_nodup {l : ℕ} (hl : l < 7) : (PE l).Nodup := by
  have h := distinctK_spec (CFSG.KS.allN_spec pdist_ok l hl)
  rw [PL, List.pairwise_map] at h
  rw [PE, List.Nodup, List.pairwise_map]
  refine h.imp fun {a b} hab e => ?_
  rw [FixCPair.peqK_of_eq (WE_rep hl a) (e ▸ WE_rep hl b)] at hab
  exact Bool.noConfusion hab

theorem RE_rep {l r : ℕ} (hl : l < 7) (hr : r < NR l) : PairRep (RE l r) (nth 0 (RL l) r) := by
  rw [RL_nth hr]
  exact WE_rep hl _

theorem words_rep {l : ℕ} (hl : l < 7) (ws : List (List ℕ)) (i : ℕ) :
    PairRep (nth 1 (ws.map (WE l)) i) (nth pidP (ws.map (EV l)) i) ∧
      PairRep (nth 1 (ws.map (WE l)) i)⁻¹ (nth pidP (ws.map fun w => EV l (invW w)) i) := by
  by_cases hi : i < ws.length
  · rw [nth_map_of_lt _ _ [] hi, nth_map_of_lt _ _ [] hi, nth_map_of_lt _ _ [] hi]
    refine ⟨WE_rep hl _, ?_⟩
    have e : (WE l (nth [] ws i))⁻¹ = WE l (invW (nth [] ws i)) := (wordE_invW _ _).symm
    rw [e]
    exact WE_rep hl _
  · rw [nth_map_ge _ _ _ (not_lt.1 hi), nth_map_ge _ _ _ (not_lt.1 hi),
      nth_map_ge _ _ _ (not_lt.1 hi), inv_one]
    exact ⟨pairRep_one, pairRep_one⟩

theorem CE_rep {l r : ℕ} (hl : l < 7) (i : ℕ) :
    PairRep (nth 1 (CE l r) i) (nth pidP (CL l r) i) ∧
      PairRep (nth 1 (CE l r) i)⁻¹ (nth pidP (CIL l r) i) :=
  words_rep hl (CWL l r) i

theorem TE_rep {l r : ℕ} (hl : l < 7) {j : ℕ} (hj : j < (TL l r).length) :
    PairRep (TE l r j) (nth 0 (TL l r) j) := by
  rw [TL, List.length_map] at hj
  rw [TL, nth_map_of_lt _ _ [] hj]
  exact pairRep_evalW (fun i => (CE_rep hl i).1) (fun i => (CE_rep hl i).2) _

end Local

section Bound

end Bound

section Final

end Final

end CertificateChecks.KernelJ4Count.FixC

end
