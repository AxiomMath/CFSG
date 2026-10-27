module

public import Certificates.Kernel.J4Q.KOrbA
public import Certificates.Kernel.J4Q.KOrbB
public import Certificates.Kernel.J4Q.X0OrbOk

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem kc_spec {c : Nat} (hc : c < 240) : kcK c = true := by
  by_cases h : c < 120
  · have k := KCA.all c h
    unfold kcA kcH at k
    have e : Nat.add (Nat.mul 120 0) c = c := by
      change 120 * 0 + c = c
      omega
    rw [e] at k
    exact k
  · have hb : c - 120 < 120 := by omega
    have k := KCB.all (c - 120) hb
    unfold kcB kcH at k
    have e : Nat.add (Nat.mul 120 1) (c - 120) = c := by
      change 120 * 1 + (c - 120) = c
      omega
    rw [e] at k
    exact k

theorem kAt_spec {k : Nat} (hk : k < 15360) : kAtK k = true := by
  have hc : Nat.div k 64 < 240 := by change k / 64 < 240; omega
  have h := allR_spec (kc_spec hc) (Nat.mod k 64) (by change k % 64 < 64; omega)
  have e : Nat.add (Nat.mul 64 (Nat.div k 64)) (Nat.mod k 64) = k := by
    change 64 * (k / 64) + k % 64 = k
    omega
  rw [e] at h
  exact h

theorem kAt_dec {k : Nat} (hk : k < 15360) :
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (kPar k) k) (andB (Nat.blt (kLab k) 12)
        (Nat.beq (CFSG.KD.KO.MSF k) (mulJ c rm (CFSG.KD.KO.MSF (kPar k)) (getN one KG (kLab k))))))
      (Nat.beq (CFSG.KD.KO.MSF k) one) (Nat.beq k 0) = true) ∧
    (Bool.rec (motive := fun _ => Bool) (Nat.blt (kPL k) (kPL (Nat.succ k))) true
        (orB (Nat.beq k 0) (Nat.beq (Nat.succ k) 15360)) = true) ∧
    kDerK k = true ∧
    (∀ g < 12, kTT k g < 15360 ∧ (kTT k g = 0 ∨ kPL (kTT k g) ≤ 12 * k + g) ∧
      mulJ c rm (CFSG.KD.KO.MSF k) (getN one KG g) = CFSG.KD.KO.MSF (kTT k g)) ∧
    (kSig k < 15360 ∧ kSigI k < 15360 ∧ kSig (kSigI k) = k) ∧
    (Bool.rec (motive := fun _ => Bool) (Nat.blt (CFSG.KD.KO.MSF (kSig k)) (CFSG.KD.KO.MSF (kSig (Nat.succ k)))) true
      (Nat.beq (Nat.succ k) 15360) = true) := by
  have h := kAt_spec hk
  unfold kAtK at h
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

theorem kPL_split (k : Nat) : kPar k * 12 + kLab k = kPL k := by
  unfold kPar kLab
  change kPL k / 12 * 12 + kPL k % 12 = kPL k
  omega

theorem kOrb_ok : oOrbOK kStep 12 idRows kOrb 15360 = true ∧
    kOrb.mats.toList.map encR = (List.range 15360).map CFSG.KD.KO.MSF ∧ ∀ X ∈ kOrb.mats.toList, WfA X := by
  have hroot : CFSG.KD.KO.MSF 0 = encR (idRows ()) := by
    have h := (kAt_dec (k := 0) (by decide)).1
    rw [enc_idRows hK]
    exact Nat.eq_of_beq_eq_true h
  exact obfs_sound (step := kStep) (nl := 12) (stepK := fun M g => mulJ c rm M (getN one KG g))
    (fun X g hX hg => kStep_enc X g hX hg) wf_idRows (cap := 15360) (bits := 15) (by decide)
    (by decide) (by decide) (MS := CFSG.KD.KO.MSF) (PAR := kPar) (LAB := kLab) (SIG := kSig) (TT := kTT)
    (SIGI := kSigI) hroot
    (fun k hk0 hk => by
      have h := (kAt_dec hk).1
      rw [nbeq_false (Nat.pos_iff_ne_zero.1 hk0)] at h
      change andB _ _ = true at h
      simp only [andB_eq, Bool.and_eq_true] at h
      exact ⟨lt_of_blt h.1, lt_of_blt h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩)
    (fun k hk g hg => by
      have h := (kAt_dec hk).2.2.2.1 g hg
      exact ⟨h.1, h.2.2⟩)
    (fun i hi => (kAt_dec hi).2.2.2.2.1.1)
    (fun k hk => (kAt_dec hk).2.2.2.2.1.2)
    (fun i hi => by
      have h := (kAt_dec (k := i) (by omega)).2.2.2.2.2
      rw [nbeq_false (by omega : Nat.succ i ≠ 15360)] at h
      exact lt_of_blt h)
    (fun k hk0 hk => by
      have h := (kAt_dec (k := k) (by omega)).2.1
      rw [nbeq_false (Nat.pos_iff_ne_zero.1 hk0), nbeq_false (by omega : Nat.succ k ≠ 15360)] at h
      rw [kPL_split, kPL_split]
      exact lt_of_blt h)
    (fun k hk g hg => by
      have h := ((kAt_dec hk).2.2.2.1 g hg).2.1
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [kPL_split]
        omega)

theorem kDer_spec {k : Nat} (hk : k < 15360) : kDerK k = true := (kAt_dec hk).2.2.1

end CertificateChecks.KernelJ4Q

end
