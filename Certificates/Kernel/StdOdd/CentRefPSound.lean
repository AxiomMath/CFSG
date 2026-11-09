module

public import Certificates.Kernel.StdOdd.CentRefP
public import CFSG.Certificates.Kernel.StdOdd.ChainPSound
public import Certificates.Kernel.StdOdd.CentPopH

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.StdOdd.ChainP CFSG.KS.StdOdd.Orbit
  CFSG.KS.StdOdd.Chain CFSG.KS.StdOdd.ChainP Matrix

theorem rchP_sound (D : CentData) {A B RK K ri : ℕ} {O : List ℕ} {Sr : List (List (List ℕ))}
    {l k : ℕ} (h : D.rchP A B RK K ri O Sr l k = true) : D.rchF A B RK K ri O Sr l k = true := by
  unfold CentData.rchP at h
  rw [forceLB_eq] at h
  rw [andB_eq, Bool.and_eq_true, forceB_eq] at h
  obtain ⟨hb, hw⟩ := h
  rw [walkP_eq _ _ _ (bd_of_bdB _ hb) (lenN_rkP D RK K ri O _)] at hw
  unfold CentData.rchF
  exact hw

theorem segP_sound (D : CentData) {A B ck m k : ℕ} (h : D.segP A B ck m k = true) :
    D.segF A B ck m k = true := by
  unfold CentData.segP at h
  rw [forceLB_eq] at h
  rw [andB_eq, Bool.and_eq_true, forceB_eq] at h
  obtain ⟨hb, hw⟩ := h
  rw [walkP_eq _ _ _ (bd_of_bdB _ hb) (lenN_ckP D ck _)] at hw
  unfold CentData.segF
  exact hw

theorem walkK_of_pt {Ms : List ℕ} {k : List ℕ → Bool} : ∀ (S : List (List ℕ)) (U : List ℕ),
    lenN U = 156 → stepsB Ms S = true →
    (∀ V, lenN V = 156 → (∀ i, ptB V i = walkElt Ms S i *ᵥ ptB U i) → k V = true) →
    walkK Ms S U k = true
  | [], U, hl, _, hk => hk U hl fun i => by rw [walkElt, Matrix.one_mulVec]
  | ms :: S, U, hl, hs, hk => by
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms)) (stepsB Ms S) = true at hs
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at hs
    obtain ⟨⟨hlen, hd⟩, hs⟩ := hs
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepL Ms ms U) fun U => walkK Ms S U k) = true
    rw [andB_eq, andB_eq, hlen, hd, Bool.true_and, Bool.true_and, forceLB_eq]
    refine walkK_of_pt S _ (by rw [lenN_stepL, hl]) hs fun V hV hpt => hk V hV fun i => ?_
    rw [hpt i, stepL_sel hl (Nat.eq_of_beq_eq_true hlen) hd i, Matrix.mulVec_mulVec, walkElt]

theorem selM_shift (off j : ℕ) : ∀ Ms ms : List ℕ,
    selM Ms (List.rec (motive := fun _ => List ℕ) List.nil
      (fun m _ ih' => List.cons (Nat.shiftRight m off) ih') ms) j = selM Ms ms (off + j)
  | [], _ => by simp [selM]
  | _ :: _, [] => by simp [selM]
  | M :: Ms, m :: ms => by
    change selM (M :: Ms) ((m >>> off) :: List.rec (motive := fun _ => List ℕ) List.nil
      (fun m _ ih' => List.cons (Nat.shiftRight m off) ih') ms) j = _
    rw [selM, selM, Nat.testBit_shiftRight, selM_shift off j Ms ms]

theorem walkElt_shiftS (Ms : List ℕ) (off j : ℕ) : ∀ S : List (List ℕ),
    walkElt Ms (shiftS S off) j = walkElt Ms S (off + j)
  | [] => rfl
  | ms :: S => by
    change walkElt Ms (List.cons (List.rec (motive := fun _ => List ℕ) List.nil
      (fun m _ ih' => List.cons (Nat.shiftRight m off) ih') ms) (shiftS S off)) j = _
    rw [walkElt, walkElt, selM_shift, walkElt_shiftS Ms off j S]

theorem recB_true {f : ℕ → Bool} : ∀ {nb : ℕ}, Nat.rec (motive := fun _ => Bool) true
    (fun b ih => andB (f b) ih) nb = true → ∀ b < nb, f b = true
  | 0, _, b, hb => absurd hb (Nat.not_lt_zero b)
  | nb + 1, h, b, hb => by
    change andB (f nb) (Nat.rec (motive := fun _ => Bool) true (fun b ih => andB (f b) ih) nb) =
      true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · exact recB_true h.2 b hb
    · exact h.1

theorem blkP_pt {Ms : List ℕ} {S : List (List ℕ)} {U : List ℕ} {n β b : ℕ} (hl : lenN U = 156)
    (h : blkP Ms S U n β b = true) {j : ℕ} (hj : j < 156) (hjn : 156 * b + j < n) :
    walkElt Ms S (156 * b + j) *ᵥ ptB U (156 * b + j) = vecB β := by
  unfold blkP at h
  rw [forceLB_eq, andB_eq, Bool.and_eq_true, forceB_eq] at h
  obtain ⟨hb, hw⟩ := h
  have hW : lenN (chunkPl U (Nat.mul 156 b) 156) = 156 := by rw [lenN_chunkPl, hl]
  rw [walkP_eq _ _ _ (bd_of_bdB _ hb) hW] at hw
  obtain ⟨V, hk, hV, hpt⟩ := walkK_sound _ _ hW hw
  have hmin : j < Nat.min 156 (Nat.sub n (Nat.mul 156 b)) := by
    change j < min 156 (n - 156 * b)
    omega
  have e : ptB V j = vecB β := by
    by_contra hc
    have hbit := (neqV_sound hV β _ j).2 ⟨hmin, hc⟩
    rw [Nat.eq_of_beq_eq_true hk, Nat.zero_testBit] at hbit
    exact Bool.false_ne_true hbit
  rw [hpt j, walkElt_shiftS, ptB_chunkPl _ _ _ _ hj] at e
  exact e

theorem walkK_of_walkBP {Ms : List ℕ} {S : List (List ℕ)} {U : List ℕ} {n β : ℕ}
    (hl : lenN U = 156) (h : walkBP Ms S U n β = true) :
    walkK Ms S U (fun V => Nat.beq (neqV V β n) 0) = true := by
  unfold walkBP at h
  rw [forceLB_eq, andB_eq, Bool.and_eq_true] at h
  refine walkK_of_pt S U hl h.1 fun V hV hpt => ?_
  have hz : neqV V β n = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    cases hc : (neqV V β n).testBit i
    · rfl
    · obtain ⟨hi, hne⟩ := (neqV_sound hV β n i).1 hc
      have hb := recB_true h.2 (i / 156) (by change i / 156 < (n + 155) / 156; omega)
      have hpt' := blkP_pt hl hb (j := i % 156) (Nat.mod_lt _ (by decide)) (by omega)
      rw [Nat.div_add_mod, ← hpt] at hpt'
      exact absurd hpt' hne
  rw [hz]
  rfl

theorem levP_sound (D : CentData) {j : ℕ} (h : D.levP j = true) : D.levOK j = true := by
  unfold CentData.levP forestP at h
  unfold CentData.levOK forestOK
  simp only [andB_eq, Bool.and_eq_true, forceLB_eq] at h ⊢
  exact ⟨h.1, h.2.1, walkK_of_walkBP (lenN_splitPl _ _ _ _) h.2.2⟩

theorem levQ_sound (D : CentData) {t j : ℕ} (h : D.levQ t j = true) : D.levOK j = true := by
  unfold CentData.levQ at h
  cases hc : Nat.ble (D.nf j) t
  · rw [hc] at h
    exact h
  · rw [hc] at h
    exact levP_sound D h

@[expose] noncomputable def CentData.levQZ (D : CentData) (t j : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (D.levOKZ j) (D.levP j) (Nat.ble (D.nf j) t)

theorem levQZ_sound (D : CentData) {t j : ℕ} (h : D.levQZ t j = true) : D.levOK j = true := by
  unfold CentData.levQZ at h
  cases hc : Nat.ble (D.nf j) t
  · rw [hc] at h
    exact D.levOK_of_levOKZ h
  · rw [hc] at h
    exact levP_sound D h

theorem startP_sound (D : CentData) {A B : ℕ} (h : D.startP A B = true) : D.startF A B = true := by
  unfold CentData.startP at h
  unfold CentData.startF startOK
  exact walkK_of_walkBP (lenN_vecsPl _) h

theorem flatC_mono {L K : ℕ} {fl : ℕ → ℕ} {F G : ℕ → ℕ → ℕ → Bool}
    (hFG : ∀ a b c, F a b c = true → G a b c = true) {q : ℕ} (h : flatC L K fl F q = true) :
    flatC L K fl G q = true := by
  unfold flatC at h ⊢
  revert h
  cases Nat.blt (q / K % L) (fl (q / (L * K)))
  · intro _
    rfl
  · exact hFG (q / (L * K)) (q / K % L) (q % K)

end CFSG.KD.StdOdd.Cent

end
