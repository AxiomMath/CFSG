module

public import Certificates.Kernel.StdOdd.CentAssemble
public import CFSG.Certificates.Kernel.StdOdd.PopHSound

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std

theorem walkK_mono {Ms : List ℕ} {k₁ k₂ : List ℕ → Bool} (hk : ∀ V, k₁ V = true → k₂ V = true) :
    ∀ (S : List (List ℕ)) (U : List ℕ), walkK Ms S U k₁ = true → walkK Ms S U k₂ = true
  | [], U, h => hk U h
  | ms :: S, U, h => by
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepL Ms ms U) fun V => walkK Ms S V k₁) = true at h
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepL Ms ms U) fun V => walkK Ms S V k₂) = true
    rw [andB_eq, Bool.and_eq_true, forceLB_eq] at h ⊢
    exact ⟨h.1, walkK_mono hk S _ h.2⟩

namespace CentData

variable (D : CentData)

@[expose] noncomputable def chunkH (d : ℕ) (PL : List ℕ) (A B q : ℕ) : Bool :=
  forceB (Nat.min 262144 (Nat.sub 3968055 (Nat.mul q 262144))) fun w =>
  popHB d (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd)
    (chunkPl PL (Nat.mul q 262144) w) w Form.fmPk Form.brPk) (nthN D.cnts q)

@[expose] noncomputable def candEndH (d A B : ℕ) (V : List ℕ) : Bool :=
  forceB (profAll (D.xB A B) (D.Kall.map Prod.fst) (D.Kall.map Prod.snd) D.CL D.s Form.fmPk
    Form.brPk) fun A' =>
  andB (andB (allIn V D.reps D.s) (popHB d (eqMaskV V D.bv D.s) D.m₀))
    (Nat.beq (Nat.land A' (andNot (andNot (full D.s) (eqMaskV V D.bv D.s)) (refMask V D.reps D.st D.s)))
      0)

@[expose] noncomputable def csegH (A B cc g m k d : ℕ) : Bool :=
  walkK (D.hLet A B) (stepsPl (Nat.shiftRight D.HW (Nat.mul (Nat.mul (Nat.mul 8
      (Nat.div (Nat.add D.s 7) 8)) (lenN (D.hLet A B))) (Nat.mul g k)))
      (Nat.div (Nat.add D.s 7) 8) D.s (Nat.min g (Nat.sub D.hD (Nat.mul g k)))
      (lenN (D.hLet A B))) (D.ccP cc k) fun V =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq (neqMask V (D.ccP cc (Nat.succ k))) 0)
      (D.candEndH d A B V) (Nat.beq (Nat.succ k) m)

theorem chunkF_of_chunkH {d : ℕ} {PL : List ℕ} {A B q : ℕ} (h : D.chunkH d PL A B q = true) :
    D.chunkF PL A B q = true := by
  unfold chunkH at h
  unfold chunkF chunkOK
  rw [forceB_eq] at h ⊢
  exact popK_of_popHB h

theorem candEnd_of_candEndH {d A B : ℕ} {V : List ℕ} (h : D.candEndH d A B V = true) :
    D.candEnd A B V = true := by
  unfold candEndH at h
  unfold candEnd
  rw [forceB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, popK_of_popHB h.1.2⟩, h.2⟩

theorem csegF_of_csegH {A B cc g m k d : ℕ} (h : D.csegH A B cc g m k d = true) :
    D.csegF A B cc g m k = true := by
  unfold csegH at h
  unfold csegF
  refine walkK_mono (fun V hV => ?_) _ _ h
  cases e : Nat.beq (Nat.succ k) m
  · rw [e] at hV
    exact hV
  · rw [e] at hV
    exact D.candEnd_of_candEndH hV

end CentData

end CFSG.KD.StdOdd.Cent
