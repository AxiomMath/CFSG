
module

public import CFSG.Literature.GL52LocalCheckInputs
public import CFSG.Certificates.Kernel.Misc.GL52MatSound

public section

namespace CertificateChecks.KernelMisc.GL52L

open CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

abbrev cG (g : G) : ℕ := mcode (g : Mat)

theorem cG_mul (g h : G) : cG (g * h) = mmulK (cG g) (cG h) := by
  rw [cG, cG, cG, Units.val_mul, mmulK_mcode]

theorem cG_one : cG 1 = idK := by
  rw [cG, Units.val_one, mcode_one]

theorem eq_iff_cG {g h : G} : g = h ↔ cG g = cG h :=
  ⟨fun e => e ▸ rfl, fun e => Units.ext (mcode_inj e)⟩

@[expose] noncomputable def letterK (cs ics : List ℕ) (l : ℤ) : ℕ :=
  if 0 < l then cs.getD (l.toNat - 1) idK else ics.getD ((-l).toNat - 1) idK

@[expose] noncomputable def wordK (cs ics : List ℕ) (w : List ℤ) : ℕ :=
  w.foldr (fun l acc => mmulK (letterK cs ics l) acc) idK

@[expose] def gK (gs : List G) : List ℕ := gs.map cG

@[expose] def giK (gs : List G) : List ℕ := gs.map fun g => cG g⁻¹

noncomputable abbrev wK (gs : List G) (w : List ℤ) : ℕ := wordK (gK gs) (giK gs) w

theorem getD_map_cG (gs : List G) (f : G → ℕ) (hf : f 1 = idK) (k : ℕ) :
    f (gs.getD k 1) = (gs.map f).getD k idK := by
  by_cases hk : k < gs.length
  · rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk),
      List.getElem_map]
  · rw [List.getD_eq_default gs 1 (by omega),
      List.getD_eq_default (gs.map f) idK (by rw [List.length_map]; omega), hf]

theorem cG_letterG (gs : List G) (l : ℤ) : cG (letterG gs l) = letterK (gK gs) (giK gs) l := by
  unfold letterG letterK
  split_ifs
  · exact getD_map_cG gs cG cG_one _
  · exact getD_map_cG gs (fun g => cG g⁻¹) (by rw [inv_one, cG_one]) _

theorem cG_wordG (gs : List G) (w : List ℤ) : cG (wordG (letterG gs) w) = wK gs w := by
  induction w with
  | nil => exact cG_one
  | cons l w ih =>
    have e : wordG (letterG gs) (l :: w) = letterG gs l * wordG (letterG gs) w := by
      simp only [wordG, List.map_cons, List.prod_cons]
    rw [e, cG_mul, ih, cG_letterG]
    rfl

theorem tblEq_rep {S T : Table} {g h : G} (hS : Rep 31 S g) (hT : Rep 31 T h) :
    tblEq 31 S T = (cG g == cG h) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← eq_iff_cG]
  constructor
  · exact eq_of_rep_tblEq hS hT
  · rintro rfl
    exact tblEq_iff.2 fun i hi => (hS i hi).trans (hT i hi).symm

theorem cmtT_rep {T X : Table} {g x : G} (hT : Rep 31 T g) (hX : Rep 31 X x) :
    cmtT T X = (mmulK (cG g) (cG x) == mmulK (cG x) (cG g)) := by
  rw [cmtT, tblEq_rep (Rep.compT hT hX) (Rep.compT hX hT), cG_mul, cG_mul]

theorem rep_wT (gs : List G) (w : List ℤ) : Rep 31 (wT gs w) (wordG (letterG gs) w) :=
  rep_wordTable gs w

theorem cmtT_wT (gs gs' : List G) (w w' : List ℤ) :
    cmtT (wT gs w) (wT gs' w') = (mmulK (wK gs w) (wK gs' w') == mmulK (wK gs' w') (wK gs w)) := by
  rw [cmtT_rep (rep_wT gs w) (rep_wT gs' w'), cG_wordG, cG_wordG]

theorem sqId_wT (gs : List G) (w : List ℤ) :
    tblEq 31 (compT 31 (wT gs w) (wT gs w)) (idT 31) = (mmulK (wK gs w) (wK gs w) == idK) := by
  rw [tblEq_rep (Rep.compT (rep_wT gs w) (rep_wT gs w)) (Rep.idT (by norm_num)), cG_mul, cG_one,
    cG_wordG]

theorem cubeId_wT (gs : List G) (w : List ℤ) :
    tblEq 31 (compT 31 (wT gs w) (compT 31 (wT gs w) (wT gs w))) (idT 31) =
      (mmulK (wK gs w) (mmulK (wK gs w) (wK gs w)) == idK) := by
  rw [tblEq_rep (Rep.compT (rep_wT gs w) (Rep.compT (rep_wT gs w) (rep_wT gs w)))
    (Rep.idT (by norm_num)), cG_mul, cG_mul, cG_one, cG_wordG]

theorem tblEq_wT_tbl (gs : List G) (w : List ℤ) (x : G) :
    tblEq 31 (wT gs w) (tbl x) = (wK gs w == cG x) := by
  rw [tblEq_rep (rep_wT gs w) (rep_tbl x), cG_wordG]

theorem tblEq_wT_comp (gs gs₁ gs₂ : List G) (w w₁ w₂ : List ℤ) :
    tblEq 31 (wT gs w) (compT 31 (wT gs₁ w₁) (wT gs₂ w₂)) =
      (wK gs w == mmulK (wK gs₁ w₁) (wK gs₂ w₂)) := by
  rw [tblEq_rep (rep_wT gs w) (Rep.compT (rep_wT gs₁ w₁) (rep_wT gs₂ w₂)), cG_mul, cG_wordG,
    cG_wordG, cG_wordG]

theorem cmtT_comp_tbl (gs₁ gs₂ : List G) (w₁ w₂ : List ℤ) (x : G) :
    cmtT (compT 31 (wT gs₁ w₁) (wT gs₂ w₂)) (tbl x) =
      (mmulK (mmulK (wK gs₁ w₁) (wK gs₂ w₂)) (cG x) ==
        mmulK (cG x) (mmulK (wK gs₁ w₁) (wK gs₂ w₂))) := by
  rw [cmtT_rep (Rep.compT (rep_wT gs₁ w₁) (rep_wT gs₂ w₂)) (rep_tbl x), cG_mul, cG_wordG,
    cG_wordG]

theorem mem_of_lookup {Q : Type*} {K : Type} [BEq K] [LawfulBEq K] {L : List (K × Q)} {k : K}
    {w : Q} (h : L.lookup k = some w) : (k, w) ∈ L := by
  induction L with
  | nil => simp [List.lookup] at h
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · simp only [List.lookup, beq_false_of_ne hk] at h
      exact List.mem_cons_of_mem _ (ih h)

@[expose] def lkW {K : Type} [DecidableEq K] (L : List (K × List ℤ)) (k : K) : List ℤ :=
  (L.lookup k).getD []

@[expose] def hasKey {K : Type} [DecidableEq K] (L : List (K × List ℤ)) (k : K) : Bool :=
  (L.lookup k).isSome

theorem mem_of_hasKey {K : Type} [DecidableEq K] {L : List (K × List ℤ)} {k : K}
    (h : hasKey L k = true) : ∃ e ∈ L, e.1 = k := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h
  exact ⟨(k, w), mem_of_lookup hw, rfl⟩

theorem lkWord_mem {Q : Type*} {K : Type} [DecidableEq K] (key : Q → K)
    (L : List (K × List ℤ)) (q : Q) : lkWord key L q ∈ ([] :: L.map Prod.snd) := by
  unfold lkWord
  cases h : L.lookup (key q) with
  | none => exact List.mem_cons_self
  | some w => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨(key q, w), mem_of_lookup h, rfl⟩)

@[expose] def nodupB : List ℕ → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

theorem nodup_of_nodupB : ∀ {l : List ℕ}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    have h1 : a ∉ l := by simpa using h.1
    exact List.nodup_cons.2 ⟨h1, nodup_of_nodupB h.2⟩

theorem strictlyIncreasing_of_pairwise : ∀ {l : List ℕ}, l.Pairwise (· < ·) →
    strictlyIncreasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictlyIncreasing_of_pairwise h.of_cons⟩

theorem keysDistinct_of_nodupB (n : ℕ) (Ts : List Table) (h : nodupB (Ts.map (key n)) = true) :
    keysDistinct n Ts = true := by
  unfold keysDistinct
  apply strictlyIncreasing_of_pairwise
  have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c h₁ h₂ => decide_eq_true ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂)))
    (fun a b => by
      rcases le_total a b with h | h
      · simp [h]
      · simp [h])
    (Ts.map (key n))
  have hnd := (List.mergeSort_perm (Ts.map (key n)) fun a b : ℕ => decide (a ≤ b)).nodup_iff.2
    (nodup_of_nodupB h)
  exact (hs.and hnd).imp fun hab => lt_of_le_of_ne (of_decide_eq_true hab.1) hab.2

end CertificateChecks.KernelMisc.GL52L

end
