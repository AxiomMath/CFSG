module

public import Certificates.Kernel.J4Q.X0Orb

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem orB_eq'' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem xAt_dec {k : Nat} (hk : k < 6720) :
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (xPar k) k) (andB (Nat.blt (xLab k) 16)
        (Nat.beq (CFSG.KD.X0O.MSF k) (mulJ c rm (CFSG.KD.X0O.MSF (xPar k)) (getN one XG (xLab k))))))
      (Nat.beq (CFSG.KD.X0O.MSF k) one) (Nat.beq k 0) = true) ∧
    (Bool.rec (motive := fun _ => Bool) (Nat.blt (xPL k) (xPL (Nat.succ k))) true
        (orB (Nat.beq k 0) (Nat.beq (Nat.succ k) 6720)) = true) ∧
    xDerK k = true ∧
    (∀ g < 16, xTT k g < 6720 ∧ (xTT k g = 0 ∨ xPL (xTT k g) ≤ 16 * k + g) ∧
      mulJ c rm (CFSG.KD.X0O.MSF k) (getN one XG g) = CFSG.KD.X0O.MSF (xTT k g)) ∧
    (xSig k < 6720 ∧ xSigI k < 6720 ∧ xSig (xSigI k) = k) ∧
    (Bool.rec (motive := fun _ => Bool) (Nat.blt (CFSG.KD.X0O.MSF (xSig k)) (CFSG.KD.X0O.MSF (xSig (Nat.succ k)))) true
      (Nat.beq (Nat.succ k) 6720) = true) := by
  have h := xAt_spec hk
  unfold xAtK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2, h3⟩, h4, ⟨h5, h6, h7⟩, h9⟩ := h
  refine ⟨h1, h2, h3, fun g hg => ?_, ⟨lt_of_blt h5, lt_of_blt h6, Nat.eq_of_beq_eq_true h7⟩, h9⟩
  have hg' := allR_spec h4 g hg
  simp only [orB_eq'', Bool.and_eq_true, Bool.or_eq_true] at hg'
  obtain ⟨⟨a1, a2⟩, a3⟩ := hg'
  refine ⟨lt_of_blt a1, ?_, Nat.eq_of_beq_eq_true a3⟩
  rcases a2 with a2 | a2
  · exact Or.inl (Nat.eq_of_beq_eq_true a2)
  · exact Or.inr (Nat.le_of_ble_eq_true a2)

theorem xPL_split (k : Nat) : xPar k * 16 + xLab k = xPL k := by
  unfold xPar xLab
  change xPL k / 16 * 16 + xPL k % 16 = xPL k
  omega

theorem x0Orb_ok : oOrbOK x0Step 16 idRows x0Orb 6720 = true ∧
    x0Orb.mats.toList.map encR = (List.range 6720).map CFSG.KD.X0O.MSF ∧ ∀ X ∈ x0Orb.mats.toList, WfA X := by
  have hroot : CFSG.KD.X0O.MSF 0 = encR (idRows ()) := by
    have h := (xAt_dec (k := 0) (by decide)).1
    rw [enc_idRows hK]
    exact Nat.eq_of_beq_eq_true h
  exact obfs_sound (step := x0Step) (nl := 16) (stepK := fun M g => mulJ c rm M (getN one XG g))
    (fun X g hX hg => x0Step_enc X g hX hg) wf_idRows (cap := 6720) (bits := 14) (by decide)
    (by decide) (by decide) (MS := CFSG.KD.X0O.MSF) (PAR := xPar) (LAB := xLab) (SIG := xSig) (TT := xTT)
    (SIGI := xSigI) hroot
    (fun k hk0 hk => by
      have h := (xAt_dec hk).1
      rw [nbeq_false (Nat.pos_iff_ne_zero.1 hk0)] at h
      change andB _ _ = true at h
      simp only [andB_eq, Bool.and_eq_true] at h
      exact ⟨lt_of_blt h.1, lt_of_blt h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩)
    (fun k hk g hg => by
      have h := (xAt_dec hk).2.2.2.1 g hg
      exact ⟨h.1, h.2.2⟩)
    (fun i hi => (xAt_dec hi).2.2.2.2.1.1)
    (fun k hk => (xAt_dec hk).2.2.2.2.1.2)
    (fun i hi => by
      have h := (xAt_dec (k := i) (by omega)).2.2.2.2.2
      rw [nbeq_false (by omega : Nat.succ i ≠ 6720)] at h
      exact lt_of_blt h)
    (fun k hk0 hk => by
      have h := (xAt_dec (k := k) (by omega)).2.1
      rw [nbeq_false (Nat.pos_iff_ne_zero.1 hk0), nbeq_false (by omega : Nat.succ k ≠ 6720)] at h
      rw [xPL_split, xPL_split]
      exact lt_of_blt h)
    (fun k hk g hg => by
      have h := ((xAt_dec hk).2.2.2.1 g hg).2.1
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [xPL_split]
        omega)

theorem xDer_spec {k : Nat} (hk : k < 6720) : xDerK k = true := (xAt_dec hk).2.2.1

end CertificateChecks.KernelJ4Q

end
