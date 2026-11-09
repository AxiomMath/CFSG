module

public import Certificates.Kernel.PermCent.K5138
public import Certificates.Kernel.PermCent.KG5123A
public import Certificates.Kernel.PermCent.KG5122
public import CFSG.Certificates.Kernel.PermCent.SylowListSound
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.Certificates.Kernel.PkCV.L34MT

open Subgroup CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
  CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkEnum

theorem conj_closure_inv {n : Nat} (gs V : Set (Equiv.Perm (Fin n)))
    (h : ∀ s ∈ gs, ∀ x ∈ V, s * x * s⁻¹ ∈ V) :
    ∀ g ∈ closure gs, ∀ x, g * x * g⁻¹ ∈ V → x ∈ V :=
  fun g hg x hx => (conj_closure_iff gs V h g hg x).2 hx

theorem conjAllC_sound (s : CV 42) (L : List (CV 42)) :
    ∀ (M : List (CV 42)) (t : List Nat), conjAllC s L M t = true →
      ∀ u ∈ M, ev s * ev u * (ev s)⁻¹ = 1 ∨ ev s * ev u * (ev s)⁻¹ ∈ L.map ev
  | [], _, _, _, hu => absurd hu List.not_mem_nil
  | u :: M, k :: t, h, y, hy => by
    rw [conjAllC, Bool.and_eq_true, eq22C_eq, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · have e : ev s * ev y * (ev s)⁻¹ = ev (L.getD k 1) := by
        rw [ev_mul', h.1, ← ev_mul', mul_inv_cancel_right]
      rw [e, List.getD_eq_getElem?_getD]
      cases hk : L[k]? with
      | none => exact Or.inl (by rw [Option.getD_none, ev_one])
      | some v =>
        rw [Option.getD_some]
        exact Or.inr (List.mem_map_of_mem (List.mem_of_getElem? hk))
    · exact conjAllC_sound s L M t h.2 y hy
  | _ :: _, [], h, _, _ => by
    rw [conjAllC] at h
    exact absurd h Bool.false_ne_true

theorem conjOKC_sound (L : List (CV 42)) :
    ∀ (S : List (CV 42)) (T : List (List Nat)), conjOKC L S T = true →
      ∀ s ∈ S, ∀ u ∈ L, ev s * ev u * (ev s)⁻¹ = 1 ∨ ev s * ev u * (ev s)⁻¹ ∈ L.map ev
  | [], _, _, _, hs => absurd hs List.not_mem_nil
  | s :: S, t :: T, h, y, hy => by
    rw [conjOKC, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact conjAllC_sound y L L t h.1
    · exact conjOKC_sound L S T h.2 y hy
  | _ :: _, [], h, _, _ => by
    rw [conjOKC] at h
    exact absurd h Bool.false_ne_true

theorem conjOK_mem {L : List (CV 42)} {T : List (List Nat)} (h : conjOKC L gAut T = true)
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ gAut.map ev) {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ L.map ev) : s * x * s⁻¹ = 1 ∨ s * x * s⁻¹ ∈ L.map ev := by
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
  exact conjOKC_sound L gAut T h s' hs' u hu

theorem conjAt_mem {L : List (CV 42)}
    (h : ∀ k < gAut.length, ∀ u ∈ L, ev (gAut.getD k 1) * ev u * (ev (gAut.getD k 1))⁻¹ = 1 ∨
      ev (gAut.getD k 1) * ev u * (ev (gAut.getD k 1))⁻¹ ∈ L.map ev)
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ gAut.map ev) {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ L.map ev) : s * x * s⁻¹ = 1 ∨ s * x * s⁻¹ ∈ L.map ev := by
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hs'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
  have h' := h k hk u hu
  rwa [List.getD_eq_getElem _ _ hk] at h'

theorem kConj3 : ∀ k < gAut.length, ∀ u ∈ clC rep3 W3.chars,
    ev (gAut.getD k 1) * ev u * (ev (gAut.getD k 1))⁻¹ = 1 ∨
      ev (gAut.getD k 1) * ev u * (ev (gAut.getD k 1))⁻¹ ∈ (clC rep3 W3.chars).map ev := by
  intro k hk u hu
  have hk5 : k < 5 := by simpa [gAut] using hk
  have hc := List.all_eq_true.1 kCls3 k (List.mem_range.2 hk5)
  rw [← kTie3.2] at hc
  exact Or.inr (clsT_mem _ _ X3 _ kTie3.1 hc u hu)

theorem hgP : QP.originalSubgroup = closure {σ | σ ∈ gP.map ev} := by
  rw [QP, certificate_originalSubgroup]
  simp only [gP, List.map_cons, List.map_nil, ev_cOf]

set_option maxRecDepth 100000 in
theorem kCentLen :((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length = 72 := by
  have hQP : ValidSchreier QP := check_certificate_of _ _ _ _ _ kQP
  have h := count_mul_orbit QP hQP gP hgP (cOf rep4) L34Orb.orbW4 XO4 L34Orb.orbR4 kOrb4
  rw [card_group QP hQP, orderCertificate_eq_orderV, KGrp.K5122.kQP] at h
  have hl : L34Orb.orbW4.length = 280 := rfl
  rw [hl] at h
  omega

theorem kCent : ((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length % 9 = 0 := by
  rw [kCentLen]

theorem k5138_neg : (tElts.all fun g => !powOneC g 2 || decide (g = 1) ||
      decide (g ∈ clC rep1 W1.chars)) = false ∧
    ((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length % 27 ≠ 0 := by
  rw [kCentLen]
  exact ⟨kNegT, by decide⟩

theorem kCover : coverC (clC rep1 W1.chars) (clC rep2 W2.chars) (clC rep3 W3.chars)
    (clC rep4 W4.chars) = true := by
  have hQA : ValidSchreier QA := check_certificate_of _ _ _ _ _ KGrp.K5123.kQA.1
  have hcard : Nat.card QA.originalSubgroup = 2 ^ 8 * 945 := by
    rw [card_group QA hQA, orderCertificate_eq_orderV, KGrp.K5123.kQA.2]
    norm_num
  have hgen : QA.originalSubgroup = closure {σ | σ ∈ gAut.map ev} := by
    rw [QA, certificate_originalSubgroup]
    simp only [gAut, List.map_cons, List.map_nil, ev_cOf]
  let V : Set (Equiv.Perm (Fin 42)) := {x | x = 1 ∨ x ∈ (clC rep1 W1.chars).map ev ∨
    x ∈ (clC rep2 W2.chars).map ev ∨ x ∈ (clC rep3 W3.chars).map ev ∨
    x ∈ (clC rep4 W4.chars).map ev}
  have hstep : ∀ s ∈ {σ | σ ∈ gAut.map ev}, ∀ x ∈ V, s * x * s⁻¹ ∈ V := by
    intro s hs x hx
    rcases hx with rfl | h1 | h2 | h3 | h4
    · exact Or.inl (by group)
    · rcases conjOK_mem kConj1 hs h1 with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · rcases conjOK_mem kConj2 hs h2 with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inl e))
    · rcases conjAt_mem kConj3 hs h3 with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · rcases conjOK_mem kConj4 hs h4 with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
  have hinv := conj_closure_inv {σ | σ ∈ gAut.map ev} V hstep
  have hR : ∀ ρ ∈ repsC, ev ρ ∈ V := by
    intro ρ hρ
    simp only [repsC, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (List.mem_map_of_mem (of_decide_eq_true kRep.1)))
    · exact Or.inr (Or.inr (Or.inl (List.mem_map_of_mem (of_decide_eq_true kRep.2.1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_map_of_mem (of_decide_eq_true kRep.2.2.1)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (List.mem_map_of_mem (of_decide_eq_true kRep.2.2.2)))))
  have key := SylL.forall_invol_of_checks QA.originalSubgroup gAut tGens repsC tElts covW
    hgen.ge ((SylL.closure_words_le gAut tGenW).trans hgen.ge) (SylL.mem_of_words tGens tEltW)
    kSylClosed kSylCover (k := 8) (m := 945) (by norm_num) kSylLen hcard (by decide)
    (fun x => x ∈ V) (fun g hg x _ h => hinv g (hgen.le hg) x h) hR
  rw [coverC, List.all_eq_true]
  intro g hg
  have hA : ev g ∈ QA.originalSubgroup :=
    (mem_elemsT QA hQA (ev g)).1 (by rw [elemsT_eq_elemsC]; exact List.mem_map_of_mem hg)
  by_cases h2 : powOneC g 2 = true
  · by_cases h1 : g = 1
    · simp [h1]
    · have h2' : ev g ^ 2 = 1 := by
        rw [← pow_fast] at h2
        rw [ev_pow', of_decide_eq_true h2, ev_one]
      have h1' : ev g ≠ 1 := fun e => h1 (ev_injective (by rw [e, ev_one]))
      rcases key (ev g) hA h2' h1' with e | e | e | e | e
      · exact absurd e h1'
      · simp [(mem_map_ev _ _).1 e]
      · simp [(mem_map_ev _ _).1 e]
      · simp [(mem_map_ev _ _).1 e]
      · simp [(mem_map_ev _ _).1 e]
  · simp [h2]

end CFSG.Certificates.Kernel.PkCV.L34MT

end
