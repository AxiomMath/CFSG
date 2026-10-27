module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.SigmaKDefs
public import Certificates.Kernel.K272036.Check

public section

namespace CertificateChecks.K272036

open CFSG.Quasithin.J2Cz CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

theorem shEval_congr {g g' : Fin 5 → ShC} {w : List (Fin 5 × Bool)}
    (h : ∀ a ∈ w, g a.1 = g' a.1) : shEval g w = shEval g' w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [shEval, List.foldr_cons] at ih ⊢
    rw [h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem enc_gK : (fun j => enc ((gK j : KK) : Model)) = shGen := funext fun j => enc_elG j

theorem relsOK_iff (g : Fin 5 → ShC) (rs : List (List (Fin 5 × Bool))) :
    relsOK g rs = true ↔ ∀ r ∈ rs, shEval g r = shOne := by
  simp [relsOK]

theorem inWords_iff (ws : List (List (Fin 5 × Bool))) (s : ShC) :
    inWords ws s = true ↔ ∃ w ∈ ws, shEval shGen w = s := by
  simp [inWords]

theorem rel_transport (σ : KK →* KK) {r : List (Fin 5 × Bool)} (hr : shEval shGen r = shOne) :
    shEval (fun j => enc ((σ (gK j) : KK) : Model)) r = shOne := by
  have h1 : evalK gK r = 1 := by
    apply Subtype.ext
    apply enc_injective
    rw [enc_evalK, enc_gK, hr, OneMemClass.coe_one, enc_one]
  rw [← enc_evalK (fun j => σ (gK j)) r, ← map_evalK σ gK r, h1, map_one, OneMemClass.coe_one,
    enc_one]

theorem sq_transport (σ : KK →* KK)
    (hsq : ∀ k : KK, ((σ (σ k) : KK) : Model) = elA * (k : Model) * elA⁻¹) (j : Fin 5)
    {w : List (Fin 5 × Bool)} (hw : shEval shGen w = enc ((σ (gK j) : KK) : Model)) :
    shEval (fun i => enc ((σ (gK i) : KK) : Model)) w = shAd (shGen j) := by
  have h1 : σ (gK j) = evalK gK w := by
    apply Subtype.ext
    apply enc_injective
    rw [enc_evalK, enc_gK, hw]
  rw [← enc_evalK (fun i => σ (gK i)) w, ← map_evalK σ gK w, ← h1, hsq, enc_mul, enc_mul, enc_inv,
    enc_elA]
  exact congrArg (fun a => shAd a) (enc_elG j)

theorem shS_ne4 {a b c : ShC} {j : Fin 5} (h : j ≠ 4) : shS a b j = shS a c j := by
  fin_cases j <;> first | rfl | exact absurd rfl h

theorem shS_ne3 {a b c : ShC} {j : Fin 5} (h : j ≠ 3) : shS a c j = shS b c j := by
  fin_cases j <;> first | rfl | exact absurd rfl h

theorem r3s_letters : ∀ r ∈ r3s, ∀ a ∈ r, a.1 ≠ 4 := by decide

theorem r4s_letters : ∀ r ∈ r4s, ∀ a ∈ r, a.1 ≠ 3 := by decide

theorem forced : ∀ σ : KK →* KK, ((σ (gK 0) : KK) : Model) = elY →
    ((σ (gK 1) : KK) : Model) = elX → ((σ (gK 2) : KK) : Model) = elZ * elX →
    (∀ k : KK, ((σ (σ k) : KK) : Model) = elA * (k : Model) * elA⁻¹) →
    ((σ (gK 3) : KK) : Model) = elT := by
  intro σ hy hx hz hsq
  set s3 := enc ((σ (gK 3) : KK) : Model) with hs3def
  set s4 := enc ((σ (gK 4) : KK) : Model) with hs4def
  have hs : (fun j => enc ((σ (gK j) : KK) : Model)) = shS s3 s4 := by
    funext j
    fin_cases j
    · show enc ((σ (gK 0) : KK) : Model) = shY
      rw [hy, enc_elY]
    · show enc ((σ (gK 1) : KK) : Model) = shX
      rw [hx, enc_elX]
    · show enc ((σ (gK 2) : KK) : Model) = shMul shZ shX
      rw [hz, enc_mul, enc_elZ, enc_elX]
    · rfl
    · rfl
  have hrel : ∀ r ∈ r3s ++ r4s ++ r5s, shEval (shS s3 s4) r = shOne := by
    have h := stageAB
    simp only [stageABWith, Bool.and_eq_true] at h
    intro r hr
    rw [← hs]
    exact rel_transport σ ((relsOK_iff _ _).1 h.1 r hr)
  have hK := stageAB
  simp only [stageABWith, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hK
  have hA := (hK.2 s3 (enc_mem_shK (σ (gK 3)).2)).1
  have hB := (hK.2 s4 (enc_mem_shK (σ (gK 4)).2)).2
  obtain ⟨w3, hw3m, hw3⟩ : ∃ w ∈ c3w, shEval shGen w = s3 := by
    refine (inWords_iff _ _).1 (hA.resolve_left ?_)
    rw [Bool.not_eq_false, relsOK_iff]
    intro r hr
    rw [shEval_congr fun a ha => shS_ne4 (r3s_letters r hr a ha)]
    exact hrel r (List.mem_append_left _ (List.mem_append_left _ hr))
  obtain ⟨w4, hw4m, hw4⟩ : ∃ w ∈ c4w, shEval shGen w = s4 := by
    refine (inWords_iff _ _).1 (hB.resolve_left ?_)
    rw [Bool.not_eq_false, relsOK_iff]
    intro r hr
    rw [shEval_congr fun a ha => shS_ne3 (r4s_letters r hr a ha)]
    exact hrel r (List.mem_append_left _ (List.mem_append_right _ hr))
  have hC := stageC
  simp only [stageCWith, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.true_and,
    beq_iff_eq] at hC
  rcases hC w3 hw3m w4 hw4m with (h | h) | h
  · apply enc_injective
    rw [enc_elT, ← hs3def, ← hw3, h]
  · exfalso
    rw [hw3, hw4] at h
    have h' : relsOK (shS s3 s4) r5s = true :=
      (relsOK_iff _ _).2 fun r hr => hrel r (List.mem_append_right _ hr)
    rw [h] at h'
    exact Bool.false_ne_true h'
  · exfalso
    have h' : sqOK w3 w4 = true := by
      simp only [sqOK, hw3, hw4, Bool.and_eq_true, beq_iff_eq]
      rw [← hs]
      exact ⟨sq_transport σ hsq 3 hw3, sq_transport σ hsq 4 hw4⟩
    rw [h] at h'
    exact Bool.false_ne_true h'

end CertificateChecks.K272036

end
