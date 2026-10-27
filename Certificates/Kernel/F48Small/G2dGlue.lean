module

public import Certificates.Kernel.F48Small.G2d
public import CFSG.Certificates.Kernel.F48Small.G2dSound

public section

namespace CertificateChecks.KernelF48S

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L CFSG.KC.Ord CFSG.Quasithin

theorem g2d_nthV (l : List ℕ) (i : ℕ) : CFSG.KC.Misc.E6Std.nthV l i = getK l i := by
  rw [getK_eq]
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem letOK_g2d : LetOK 28 5 burnsideF48s_g2dGL burnsideF48s_g2dGLi :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem g2d_evL (w : List (Fin 5 × Bool)) :
    burnsideF48s_g2dEvL w = burnsideF48s_eEvL 28 burnsideF48s_g2dGL burnsideF48s_g2dGLi w := rfl

theorem g2d_letVal : ∀ l : Fin 5 × Bool, ValG (burnsideF48s_g2dLetL l) := by
  unfold ValG
  decide +kernel

theorem g2d_val_range : ValG (List.range 28) :=
  ⟨by simp, fun e he => by simp at he; omega⟩

theorem g2d_val (w : List (Fin 5 × Bool)) : ValG (burnsideF48s_g2dEvL w) :=
  valG_foldl _ g2d_letVal w _ g2d_val_range

theorem g2d_enc (w : List (Fin 5 × Bool)) : encL (burnsideF48s_g2dEvL w) = ekG2d w := by
  rw [g2d_evL]
  exact encL_ev letOK_g2d w

theorem g2d_val_compL {x y : List ℕ} (hx : ValG x) (hy : ValG y) : ValG (compL x y) :=
  valG_compL hx hy

theorem g2d_enc_compL {x y : List ℕ} (hx : ValG x) (hy : ValG y) :
    encL (compL x y) = pcomp (encL x) 28 (encL y) :=
  encL_compL_g hx hy

theorem g2d_eq_of_enc {x y : List ℕ} (hx : ValG x) (hy : ValG y) (h : encL x = encL y) :
    x = y :=
  eq_of_encL_g hx hy h

theorem g2d_getD_map_range {α : Type} (f : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  simp [hi]

theorem g2d_T {k : ℕ} (hk : k < 32) :
    getK G2dT.V k = encL (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF k)) := by
  have h := G2dT.all k hk
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFT]

theorem g2d_Ti {k : ℕ} (hk : k < 32) :
    getK G2dTi.V k = encL (burnsideF48s_g2dEvL (burnsideF48s_invW (burnsideF48s_g2dTelF k))) := by
  have h := G2dTi.all k hk
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFTi]

theorem g2d_A {k : ℕ} (hk : k < 64) :
    getK G2dA.V k = encL (burnsideF48s_g2dEvL (burnsideF48s_g2dAF k)) := by
  have h := G2dA.all k hk
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFA]

theorem g2d_A8 {k : ℕ} (hk : k < 8) :
    getK G2dA8.V k = encL (burnsideF48s_g2dEvL (burnsideF48s_g2dAF k)) := by
  have h := G2dA8.all k hk
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFA]

theorem g2d_B {k : ℕ} (hk : k < 64) :
    getK G2dB.V k = encL (burnsideF48s_g2dEvL (burnsideF48s_g2dBF k)) := by
  have h := G2dB.all k hk
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFB]

theorem g2d_V {k : ℕ} (hk : k < 4) :
    getK G2dV.V k = encL (burnsideF48s_g2dEvL (u33Word (burnsideF48s_g2dCandV.getD k ""))) := by
  have h := G2dV.all k hk
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFV]

theorem g2d_W0 : getK G2dW.V 0 = encL (burnsideF48s_g2dEvL (u33Word "Xs")) := by
  have h := G2dW.all 0 (by decide)
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFW]
  rfl

theorem g2d_W1 : getK G2dW.V 1 = encL (burnsideF48s_g2dEvL (u33Word "Y")) := by
  have h := G2dW.all 1 (by decide)
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFW]
  rfl

theorem g2d_W2 : getK G2dW.V 2 = encL (burnsideF48s_g2dEvL (u33Word "X")) := by
  have h := G2dW.all 2 (by decide)
  rw [Nat.beq_eq, g2d_nthV] at h
  rw [← h, g2d_enc, g2dFW]
  rfl

theorem g2d_id : g2dId = encL (List.range 28) := rfl

theorem g2d_T_len : G2dT.V.length = 32 := rfl

theorem g2d_A8_len : G2dA8.V.length = 8 := rfl

theorem g2d_B_len : G2dB.V.length = 64 := rfl

theorem g2d_mem_getK {l : List ℕ} {k : ℕ} (hk : k < l.length) : getK l k ∈ l := by
  rw [getK_eq, List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem g2d_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) : ∃ k < l.length, getK l k = x := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  exact ⟨k, hk, by rw [getK_eq, List.getD_eq_getElem _ _ hk]⟩

theorem g2dRel1_ok : burnsideF48s_g2dEvL (burnsideF48s_g2dCand 1) = List.range 28 := by
  refine g2d_eq_of_enc (g2d_val _) g2d_val_range ?_
  rw [g2d_enc, ← g2d_id]
  exact Nat.eq_of_beq_eq_true g2d_rel1

theorem g2dRel3_ok : burnsideF48s_g2dEvL (burnsideF48s_g2dCand 3) = List.range 28 := by
  refine g2d_eq_of_enc (g2d_val _) g2d_val_range ?_
  rw [g2d_enc, ← g2d_id]
  exact Nat.eq_of_beq_eq_true g2d_rel3

theorem g2dCheckA_ok : burnsideF48s_g2dCheckA () = true := by
  simp only [burnsideF48s_g2dCheckA, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq]
  intro i₁ h₁ i₂ h₂
  rw [burnsideF48s_g2dTL, g2d_getD_map_range _ h₁, g2d_getD_map_range _ h₂]
  have hv := g2d_val_compL (g2d_val_compL (g2d_val (burnsideF48s_g2dTelF i₁))
    (g2d_val (u33Word "X"))) (g2d_val (burnsideF48s_g2dTelF i₂))
  have he : encL (compL (compL (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i₁))
      (burnsideF48s_g2dEvL (u33Word "X"))) (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i₂))) =
      pcomp (pcomp (getK G2dT.V i₁) 28 (getK G2dW.V 2)) 28 (getK G2dT.V i₂) := by
    rw [g2d_enc_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _),
      g2d_enc_compL (g2d_val _) (g2d_val _), g2d_T h₁, g2d_T h₂, g2d_W2]
  have hc := g2d_checkA
  simp only [g2dCheckATw, allA_eq, List.all_eq_true, orB_eq, notB_eq, anyA_eq,
    Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at hc
  rcases hc _ (g2d_mem_getK (by rw [g2d_T_len]; exact h₁)) _
    (g2d_mem_getK (by rw [g2d_T_len]; exact h₂)) with hn | ⟨x, hx, hxe⟩
  · left
    intro hsq
    have h2 := congrArg encL hsq
    rw [g2d_enc_compL hv hv, he, ← g2d_id] at h2
    rw [h2] at hn
    simp at hn
  · right
    obtain ⟨k, hk, rfl⟩ := g2d_of_mem hx
    have hk8 : k < 8 := by rwa [g2d_A8_len] at hk
    refine ⟨k, hk8, g2d_eq_of_enc hv ?_ ?_⟩
    · rw [burnsideF48s_g2dAL, g2d_getD_map_range _ (by omega : k < 64)]
      exact g2d_val _
    · rw [burnsideF48s_g2dAL, g2d_getD_map_range _ (by omega : k < 64), he, ← g2d_A8 hk8]
      exact Nat.eq_of_beq_eq_true hxe

theorem g2dCheckB_ok : burnsideF48s_g2dCheckB () = true := by
  simp only [burnsideF48s_g2dCheckB, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq]
  intro i₁ h₁ i₂ h₂
  rw [burnsideF48s_g2dTL, g2d_getD_map_range _ h₁, g2d_getD_map_range _ h₂]
  have hv := g2d_val_compL (g2d_val_compL (g2d_val (burnsideF48s_g2dTelF i₁))
    (g2d_val (u33Word "Y"))) (g2d_val (burnsideF48s_g2dTelF i₂))
  have he : encL (compL (compL (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i₁))
      (burnsideF48s_g2dEvL (u33Word "Y"))) (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i₂))) =
      pcomp (pcomp (getK G2dT.V i₁) 28 (getK G2dW.V 1)) 28 (getK G2dT.V i₂) := by
    rw [g2d_enc_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _),
      g2d_enc_compL (g2d_val _) (g2d_val _), g2d_T h₁, g2d_T h₂, g2d_W1]
  have hc := g2d_checkB
  simp only [g2dCheckBTw, allA_eq, List.all_eq_true, anyA_eq, List.any_eq_true] at hc
  obtain ⟨x, hx, hxe⟩ := hc _ (g2d_mem_getK (by rw [g2d_T_len]; exact h₁)) _
    (g2d_mem_getK (by rw [g2d_T_len]; exact h₂))
  obtain ⟨k, hk, rfl⟩ := g2d_of_mem hx
  have hk64 : k < 64 := by rwa [g2d_B_len] at hk
  refine ⟨k, hk64, g2d_eq_of_enc hv ?_ ?_⟩
  · rw [burnsideF48s_g2dBL, g2d_getD_map_range _ hk64]
    exact g2d_val _
  · rw [burnsideF48s_g2dBL, g2d_getD_map_range _ hk64, he, ← g2d_B hk64]
    exact Nat.eq_of_beq_eq_true hxe

theorem g2d_candAll {a : ℕ} (ha : a < 8) : walkC g2dCandP a g2dTri 0 = true := by
  interval_cases a
  exacts [g2d_cand0, g2d_cand1, g2d_cand2, g2d_cand3, g2d_cand4, g2d_cand5, g2d_cand6, g2d_cand7]

theorem g2d_tri_len : g2dTri.length = 4096 := by
  decide +kernel

theorem g2d_cs (k : ℕ) :
    burnsideF48s_g2dTab.toList.toArray.getD k '0' = G2dTab.chars.getD k '0' := by
  rw [G2dTab.eq, String.toList_ofList]
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.size_toArray, List.getElem_toArray]
  split <;> simp_all

theorem g2dCheckCand_ok : burnsideF48s_g2dCheckCand () = true := by
  simp only [burnsideF48s_g2dCheckCand, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, g2d_cs]
  intro a ha b hb c hc
  have he4 : 512 * a + 8 * b + c < 4096 := by omega
  have hw := walkC_sound g2dCandP a g2dTri 0 (g2d_candAll ha) (512 * a + 8 * b + c)
    (by rw [g2d_tri_len]; exact he4) (by omega)
  have hdig := triK_getD burnsideF48s_g2dDig (512 * a + 8 * b + c) G2dTab.chars
    (by rw [g2d_chars_length]; omega)
  have h1 : (0 + (512 * a + 8 * b + c)) / 512 = a := by omega
  have h2 : (0 + (512 * a + 8 * b + c)) / 8 % 64 = b := by omega
  have h3 : (0 + (512 * a + 8 * b + c)) % 8 = c := by omega
  rw [g2dTri] at hw
  rw [hdig, h1, h2, h3, g2dCandP, candAt_iff] at hw
  dsimp only at hw
  obtain ⟨hj, ht, hr, e1, e2, e3⟩ := hw
  simp only [burnsideF48s_g2dTL, burnsideF48s_g2dTiL, burnsideF48s_g2dAL, burnsideF48s_g2dBL,
    burnsideF48s_g2dVL]
  rw [g2d_getD_map_range _ (by omega : a < 64), g2d_getD_map_range _ (by omega : c < 64),
    g2d_getD_map_range _ hb]
  simp (disch := omega) only [g2d_getD_map_range]
  refine ⟨⟨⟨⟨⟨hj, ht⟩, hr⟩, ?_⟩, ?_⟩, ?_⟩
  · refine g2d_eq_of_enc (g2d_val_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _))
      (g2d_val _) ?_
    rw [g2d_enc_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _),
      g2d_enc_compL (g2d_val _) (g2d_val _), ← g2d_T ht, ← g2d_A (by omega), ← g2d_Ti ht,
      ← g2d_W0]
    exact e1
  · refine g2d_eq_of_enc (g2d_val_compL (g2d_val_compL (g2d_val_compL (g2d_val _) (g2d_val _))
      (g2d_val _)) (g2d_val _)) (g2d_val _) ?_
    rw [g2d_enc_compL (g2d_val_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _))
      (g2d_val _), g2d_enc_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _),
      g2d_enc_compL (g2d_val _) (g2d_val _), ← g2d_T ht, ← g2d_B hb, ← g2d_Ti ht, ← g2d_T hr,
      ← g2d_W1]
    exact e2
  · refine g2d_eq_of_enc (g2d_val_compL (g2d_val_compL (g2d_val _)
      (g2d_val_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _))) (g2d_val _))
      (g2d_val _) ?_
    rw [g2d_enc_compL (g2d_val_compL (g2d_val _)
        (g2d_val_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _))) (g2d_val _),
      g2d_enc_compL (g2d_val _) (g2d_val_compL (g2d_val_compL (g2d_val _) (g2d_val _))
        (g2d_val _)),
      g2d_enc_compL (g2d_val_compL (g2d_val _) (g2d_val _)) (g2d_val _),
      g2d_enc_compL (g2d_val _) (g2d_val _), ← g2d_T ht, ← g2d_A (by omega), ← g2d_Ti ht,
      ← g2d_T hr, ← g2d_Ti hr, ← g2d_V hj]
    exact e3

theorem certificate7533_facts : burnsideF48s_g2dCheckGens () = true ∧
    burnsideF48s_g2dCheckA () = true ∧ burnsideF48s_g2dCheckB () = true ∧
    burnsideF48s_g2dCheckCand () = true ∧
    burnsideF48s_g2dEvL (burnsideF48s_g2dCand 1) = List.range 28 ∧
    burnsideF48s_g2dEvL (burnsideF48s_g2dCand 3) = List.range 28 :=
  ⟨g2d_gens, g2dCheckA_ok, g2dCheckB_ok, g2dCheckCand_ok, g2dRel1_ok, g2dRel3_ok⟩

end CertificateChecks.KernelF48S
