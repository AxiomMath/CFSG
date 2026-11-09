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

@[expose] noncomputable def letterSumZ (Ms ms U : List ℕ) : ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ) (fun _ => nat_lit 0)
    (fun M _ ih ms => List.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun m ms' _ => Bool.rec (motive := fun _ => ℕ) (Nat.xor (Nat.land m (rowX M U)) (ih ms'))
        (ih ms') (Nat.beq m 0)) ms) Ms ms

@[expose] noncomputable def stepAuxZ (ms U : List ℕ) (o : ℕ) (V Ms : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun _ => List.nil)
    (fun x _ ih Ms => List.cons (Nat.xor (andNot x o) (letterSumZ Ms ms U)) (ih (shiftRows Ms)))
    V Ms

@[expose] noncomputable def walkKZ (Ms : List ℕ) (S : List (List ℕ)) (U : List ℕ)
    (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun U => k U)
    (fun ms _ ih U => andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepAuxZ ms U (orL ms) U Ms) ih)) S U

theorem letterSumZ_eq : ∀ (Ms ms U : List ℕ), letterSumZ Ms ms U = letterSum Ms ms U
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | M :: Ms, m :: ms, U => by
    change Bool.rec (motive := fun _ => ℕ) (Nat.xor (Nat.land m (rowX M U)) (letterSumZ Ms ms U))
      (letterSumZ Ms ms U) (Nat.beq m 0) = Nat.xor (Nat.land m (rowX M U)) (letterSum Ms ms U)
    rw [letterSumZ_eq Ms ms U]
    cases e : Nat.beq m 0
    · rfl
    · have e0 : m = 0 := Nat.eq_of_beq_eq_true e
      subst e0
      change letterSum Ms ms U = Nat.xor (Nat.land 0 (rowX M U)) (letterSum Ms ms U)
      have h0 : Nat.land 0 (rowX M U) = 0 := Nat.zero_and _
      rw [h0]
      exact (Nat.zero_xor _).symm

theorem stepAuxZ_eq (ms U : List ℕ) (o : ℕ) :
    ∀ (V Ms : List ℕ), stepAuxZ ms U o V Ms = stepAux ms U o V Ms
  | [], _ => rfl
  | x :: V, Ms => by
    change List.cons (Nat.xor (andNot x o) (letterSumZ Ms ms U)) (stepAuxZ ms U o V (shiftRows Ms)) =
      List.cons (Nat.xor (andNot x o) (letterSum Ms ms U)) (stepAux ms U o V (shiftRows Ms))
    rw [letterSumZ_eq, stepAuxZ_eq ms U o V]

theorem walkKZ_eq (Ms : List ℕ) (k : List ℕ → Bool) :
    ∀ (S : List (List ℕ)) (U : List ℕ), walkKZ Ms S U k = walkK Ms S U k
  | [], _ => rfl
  | ms :: S, U => by
    change andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
        (forceLB (stepAuxZ ms U (orL ms) U Ms) fun V => walkKZ Ms S V k) =
      andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
        (forceLB (stepL Ms ms U) fun V => walkK Ms S V k)
    rw [stepAuxZ_eq]
    have hf : (fun V => walkKZ Ms S V k) = fun V => walkK Ms S V k :=
      funext fun V => walkKZ_eq Ms k S V
    rw [hf]
    rfl

@[expose] noncomputable def forestZ (FPn WN bw n D : ℕ) (Ms : List ℕ) (β : ℕ) : Bool :=
  forceLB (splitPl FPn bw n 156) fun F => andB (sortOK F n)
    (walkKZ Ms (stepsPl WN bw n D (lenN Ms)) F fun V => Nat.beq (neqV V β n) 0)

theorem forestZ_eq (FPn WN bw n D : ℕ) (Ms : List ℕ) (β : ℕ) :
    forestZ FPn WN bw n D Ms β = forestOK FPn WN bw n D Ms β := by
  unfold forestZ forestOK
  simp only [walkKZ_eq]

namespace CentData

variable (D : CentData)

@[expose] noncomputable def levOKZ (j : ℕ) : Bool :=
  andB (CFSG.KC.LQT.P.allL (D.RI j) fun r => andB (Nat.blt r (lenN D.V)) (fixesOK (nthV D.V r) D.βs j))
    (forestZ (D.FP j) (D.WN j) (Nat.div (Nat.add (D.nf j) 7) 8) (D.nf j) (D.Df j)
      ((D.RI j).map (nthV D.V)) (nthN D.βs j))

theorem levOK_of_levOKZ {j : ℕ} (h : D.levOKZ j = true) : D.levOK j = true := by
  unfold levOKZ at h
  unfold levOK
  rwa [forestZ_eq] at h

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

@[expose] noncomputable def csegZ (A B cc g m k d : ℕ) : Bool :=
  walkKZ (D.hLet A B) (stepsPl (Nat.shiftRight D.HW (Nat.mul (Nat.mul (Nat.mul 8
      (Nat.div (Nat.add D.s 7) 8)) (lenN (D.hLet A B))) (Nat.mul g k)))
      (Nat.div (Nat.add D.s 7) 8) D.s (Nat.min g (Nat.sub D.hD (Nat.mul g k)))
      (lenN (D.hLet A B))) (D.ccP cc k) fun V =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq (neqMask V (D.ccP cc (Nat.succ k))) 0)
      (D.candEndH d A B V) (Nat.beq (Nat.succ k) m)

theorem csegH_of_csegZ {A B cc g m k d : ℕ} (h : D.csegZ A B cc g m k d = true) :
    D.csegH A B cc g m k d = true := by
  unfold csegZ at h
  unfold csegH
  rwa [walkKZ_eq] at h

@[expose] noncomputable def lsegZ (j cc g m k : ℕ) : Bool :=
  walkKZ ((D.RI j).map (nthV D.V)) (stepsPl (Nat.shiftRight (D.WN j) (Nat.mul (Nat.mul (Nat.mul 8
      (Nat.div (Nat.add (D.nf j) 7) 8)) (lenN (D.RI j))) (Nat.mul g k)))
      (Nat.div (Nat.add (D.nf j) 7) 8) (D.nf j) (Nat.min g (Nat.sub (D.Df j) (Nat.mul g k)))
      (lenN (D.RI j))) (D.lcP j cc k) fun V =>
    Bool.rec (motive := fun _ => Bool) (Nat.beq (neqMask V (D.lcP j cc (Nat.succ k))) 0)
      (Nat.beq (neqV V (nthN D.βs j) (D.nf j)) 0) (Nat.beq (Nat.succ k) m)

theorem lsegF_of_lsegZ {j cc g m k : ℕ} (h : D.lsegZ j cc g m k = true) :
    D.lsegF j cc g m k = true := by
  unfold lsegZ at h
  unfold lsegF
  rwa [walkKZ_eq] at h

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
