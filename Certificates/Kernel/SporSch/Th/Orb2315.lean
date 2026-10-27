
module

public import Certificates.Kernel.SporSch.Th.Orb2315Base

public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CertificateChecks.KernelSporSch.ThOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native
open CFSG.Sporadic.ThSchreier (rowsLX rowsLY rowsT rowsVInv orbTable orbRows orbPar orbLab orbEdge
  conjRowsH orbitChecks centOrbitPar centOrbitLab centOrbitEdges transporterWord invWord abRows
  abLetterRows signedRows natsOf)
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThOrbK

theorem word_eq : ∀ w : List Int, w ≠ [] →
    CFSG.Sporadic.Th.Max3.prodRows (w.map abLetterRows) = rowsV (unpk (wordR ThO.A ThO.B ThO.BB w))
  | [], h => absurd rfl h
  | [z], _ => by
    rw [List.map_cons, List.map_nil, CFSG.Sporadic.Th.Max3.prodRows_cons,
      CFSG.Sporadic.Th.Max3.prodRows_nil, letter z, mulRowsId_sound fun i _ => unpk_lt _ i]
    rfl
  | z :: z' :: t, _ => by
    rw [List.map_cons, CFSG.Sporadic.Th.Max3.prodRows_cons,
      word_eq (z' :: t) (List.cons_ne_nil _ _), letter z, mulPk_sound]
    rfl

theorem abRows_eq {w : List Int} (hw : w ≠ []) {M : Nat}
    (h : Nat.beq (wordR ThO.A ThO.B ThO.BB w) M = true) : abRows w = rowsV (unpk M) := by
  rw [abRows, signedRows, word_eq w hw, Nat.eq_of_beq_eq_true h]

theorem rowsLX_eq : rowsLX = rowsV (unpk ThO.X) := abRows_eq (by simp [xWord]) wX

theorem rowsLY_eq : rowsLY = rowsV (unpk ThO.Y) := abRows_eq (by simp [yWord]) wY

theorem rowsV_eq : CFSG.Sporadic.ThSchreier.rowsV = rowsV (unpk ThO.V) :=
  abRows_eq (by simp [transporterWord]) wV

theorem rowsVInv_eq : rowsVInv = rowsV (unpk ThO.VI) :=
  abRows_eq (by simp [invWord, transporterWord]) wVI

theorem rowsT_eq : rowsT = rowsV (unpk ThO.T) := by
  rw [rowsT, rowsVInv_eq, rowsA_eq, rowsV_eq, mulPk_sound, mulPk_sound, Nat.eq_of_beq_eq_true bT]

theorem conj1 (m : Nat) :
    conjRowsH 1 (rowsV (unpk m)) = rowsV (unpk (mulPk (mulPk ThO.X m) ThO.X)) := by
  rw [conjRowsH, ite_eq_left rfl, rowsLX_eq, mulPk_sound, mulPk_sound]

theorem conj2 (m : Nat) :
    conjRowsH 2 (rowsV (unpk m)) = rowsV (unpk (mulPk (mulPk ThO.Y m) ThO.YY)) := by
  rw [conjRowsH, ite_eq_right (by decide), rowsLY_eq, mulPk_sound, mulPk_sound, mulPk_sound,
    Nat.eq_of_beq_eq_true bYY]

theorem rows_eq : ∀ i, i < 819 → orbRows i = rowsV (unpk (ThO.S (ThO.SG i))) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨_, _, h3, h4, _⟩ := hent i hi
    rw [orbRows]
    by_cases i0 : i = 0
    · subst i0
      rw [dite_eq_right (by omega), h3 rfl, rowsT_eq]
    · obtain ⟨p1, p2, p3⟩ := h4 i0
      have hp := par_eq i hi
      have cond : 0 < i ∧ orbPar i < i := ⟨by omega, by rw [hp]; exact p1⟩
      rw [dite_eq_left cond, ih (orbPar i) cond.2 (by omega), hp, lab_eq i hi]
      obtain ⟨_, _, _, _, _, _, q7, q8⟩ := hent (ThO.PAR i) (by omega)
      rcases p2 with l | l
      · rw [l] at p3 ⊢
        rw [conj1, q7]
        congr 4
      · rw [l] at p3 ⊢
        rw [conj2, q8]
        congr 4

theorem tab_get (i : Nat) (hi : i < 819) :
    orbTable[i]! = rowsV (unpk (ThO.S (ThO.SG i))) := by
  rw [orbTable, getElem!_pos _ i (by simp only [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  exact rows_eq i hi

theorem distinct (i j : Nat) (hi : i < 819) (hj : j < i) :
    (!eqRows orbTable[i]! orbTable[j]!) = true := by
  rw [tab_get i hi, tab_get j (by omega)]
  rcases Bool.eq_false_or_eq_true (eqRows (rowsV (unpk (ThO.S (ThO.SG i))))
    (rowsV (unpk (ThO.S (ThO.SG j))))) with hq | hq
  · exfalso
    obtain ⟨gi, ti, _⟩ := hent i hi
    obtain ⟨gj, tj, _⟩ := hent j (by omega)
    have hr := eqRows_sound (fun r _ => unpk_lt _ r) (fun r _ => unpk_lt _ r) hq
    have he : ThO.S (ThO.SG i) = ThO.S (ThO.SG j) := by
      rw [← (hsrt _ gi).1, ← (hsrt _ gj).1]
      exact repk_congr hr
    have hg := s_inj gi gj he
    have : i = j := by rw [← ti, ← tj, hg]
    omega
  · rw [hq]
    rfl

theorem facts : orbitChecks orbTable = true := by
  unfold orbitChecks
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [orbTable, Array.size_ofFn]
    rfl
  · rw [List.all_eq_true]
    intro i hm
    rw [List.mem_range] at hm
    obtain ⟨_, _, _, h4, h5, h6, h7, h8⟩ := hent i hm
    rw [edge1 i hm, edge2 i hm, tab_get i hm, tab_get _ h5, tab_get _ h6, conj1, conj2, h7, h8,
      eqRows_refl, eqRows_refl]
    simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, h5, h6, and_true,
      Bool.or_eq_true, beq_iff_eq]
    by_cases i0 : i = 0
    · exact Or.inl i0
    · obtain ⟨p1, p2, _⟩ := h4 i0
      rw [par_eq i hm, lab_eq i hm]
      exact Or.inr ⟨p1, p2⟩
  · rw [List.all_eq_true]
    intro i hm
    rw [List.mem_range] at hm
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    exact distinct i j hm hj

end CertificateChecks.KernelSporSch.ThOrb

end
