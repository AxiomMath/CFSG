module

public import Certificates.Kernel.J4Q.X0Base
public import CFSG.Certificates.Kernel.J4Q.RepMOrb
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def xcStepK (M g : Nat) : Nat :=
  mulJ c rm (mulJ c rm (getN one XG (Nat.mod (Nat.add g 8) 16)) M) (getN one XG g)

@[expose] noncomputable def ccK (MS P T S I : List Nat) (r cap k : Nat) : Bool :=
  andB (andB (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (Nat.div (getN 0 P k) 16) k)
        (Nat.beq (getN one MS k) (xcStepK (getN one MS (Nat.div (getN 0 P k) 16)) (Nat.mod (getN 0 P k) 16))))
      (Nat.beq (getN one MS k) r) (Nat.beq k 0))
      (Bool.rec (motive := fun _ => Bool) (Nat.blt (getN 0 P k) (getN 0 P (Nat.succ k))) true
        (orB (Nat.beq k 0) (Nat.beq (Nat.succ k) cap))))
    (andB (allR 16 fun g => (fun t => andB (andB (Nat.blt t cap)
          (orB (Nat.beq t 0) (Nat.ble (getN 0 P t) (Nat.add (Nat.mul 16 k) g))))
        (Nat.beq (xcStepK (getN one MS k) g) (getN one MS t))) (getN 0 T (Nat.add (Nat.mul 16 k) g)))
      (andB (andB (Nat.blt (getN 0 S k) cap) (andB (Nat.blt (getN 0 I k) cap) (Nat.beq (getN 0 S (getN 0 I k)) k)))
        (Bool.rec (motive := fun _ => Bool)
          (Nat.blt (getN one MS (getN 0 S k)) (getN one MS (getN 0 S (Nat.succ k)))) true
          (Nat.beq (Nat.succ k) cap))))

@[expose] noncomputable def ctK (k : Nat) : Bool := ccK CT CTP CTT CTS CTI (etaK c rm one Us 178) 84 k

@[expose] noncomputable def czK (k : Nat) : Bool := ccK CZ CZP CZT CZS CZI (etaK c rm one Us 407) 7 k

#j4q_all CFSG.KD.J4Q.CTC CertificateChecks.KernelJ4Q.ctK 84
#j4q_all CFSG.KD.J4Q.CZC CertificateChecks.KernelJ4Q.czK 7

theorem orB_eq3 (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem xconj_ok {MS P T S I : List Nat} {r cap bits c0 : Nat} (hr : r = etaK c rm one Us c0)
    (hcap : cap < 2 ^ bits) (h32 : 4 * 2 ^ bits < 2 ^ 32) (hpos : 0 < cap)
    (h : ∀ k < cap, ccK MS P T S I r cap k = true) :
    oOrbOK x0CStep 16 (x0Eta c0) (obfs x0CStep 16 (x0Eta c0) cap bits) cap = true ∧
      (obfs x0CStep 16 (x0Eta c0) cap bits).mats.toList.map encR = (List.range cap).map (getN one MS) ∧
      ∀ X ∈ (obfs x0CStep 16 (x0Eta c0) cap bits).mats.toList, WfA X := by
  have hd : ∀ k < cap, ((Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt (Nat.div (getN 0 P k) 16) k)
        (Nat.beq (getN one MS k) (xcStepK (getN one MS (Nat.div (getN 0 P k) 16)) (Nat.mod (getN 0 P k) 16))))
      (Nat.beq (getN one MS k) r) (Nat.beq k 0) = true) ∧
      (Bool.rec (motive := fun _ => Bool) (Nat.blt (getN 0 P k) (getN 0 P (Nat.succ k))) true
        (orB (Nat.beq k 0) (Nat.beq (Nat.succ k) cap)) = true)) ∧
      (allR 16 (fun g => (fun t => andB (andB (Nat.blt t cap)
          (orB (Nat.beq t 0) (Nat.ble (getN 0 P t) (Nat.add (Nat.mul 16 k) g))))
        (Nat.beq (xcStepK (getN one MS k) g) (getN one MS t))) (getN 0 T (Nat.add (Nat.mul 16 k) g))) = true ∧
      ((Nat.blt (getN 0 S k) cap = true ∧ Nat.blt (getN 0 I k) cap = true ∧
        Nat.beq (getN 0 S (getN 0 I k)) k = true) ∧
        Bool.rec (motive := fun _ => Bool)
          (Nat.blt (getN one MS (getN 0 S k)) (getN one MS (getN 0 S (Nat.succ k)))) true
          (Nat.beq (Nat.succ k) cap) = true)) := fun k hk => by
    have hk' := h k hk
    unfold ccK at hk'
    simp only [andB_eq, Bool.and_eq_true] at hk'
    exact hk'
  have hsplit : ∀ k, Nat.div (getN 0 P k) 16 * 16 + Nat.mod (getN 0 P k) 16 = getN 0 P k := fun k => by
    change getN 0 P k / 16 * 16 + getN 0 P k % 16 = getN 0 P k
    omega
  obtain ⟨hw, he⟩ := eta_enc c0
  refine obfs_sound (step := x0CStep) (nl := 16) (stepK := xcStepK)
    (fun X g hX hg => x0CStep_enc X g hX hg) hw hcap h32 hpos (MS := getN one MS)
    (PAR := fun k => Nat.div (getN 0 P k) 16) (LAB := fun k => Nat.mod (getN 0 P k) 16)
    (TT := fun k g => getN 0 T (Nat.add (Nat.mul 16 k) g)) (SIG := getN 0 S) (SIGI := getN 0 I)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h0 := (hd 0 hpos).1.1
    change Nat.beq (getN one MS 0) r = true at h0
    rw [Nat.eq_of_beq_eq_true h0, hr]
    exact he.symm
  · intro k hk0 hk
    have h1 := (hd k hk).1.1
    rw [nbeq_false (Nat.pos_iff_ne_zero.1 hk0)] at h1
    change andB _ _ = true at h1
    rw [andB_eq, Bool.and_eq_true] at h1
    exact ⟨lt_of_blt h1.1, Nat.mod_lt _ (by decide), Nat.eq_of_beq_eq_true h1.2⟩
  · intro k hk g hg
    have h1 := allR_spec (hd k hk).2.1 g hg
    simp only [andB_eq, Bool.and_eq_true] at h1
    exact ⟨lt_of_blt h1.1.1, Nat.eq_of_beq_eq_true h1.2⟩
  · intro i hi
    exact lt_of_blt (hd i hi).2.2.1.1
  · intro k hk
    exact ⟨lt_of_blt (hd k hk).2.2.1.2.1, Nat.eq_of_beq_eq_true (hd k hk).2.2.1.2.2⟩
  · intro i hi
    have h1 := (hd i (by omega)).2.2.2
    rw [nbeq_false (by omega : Nat.succ i ≠ cap)] at h1
    exact lt_of_blt h1
  · intro k hk0 hk
    have h1 := (hd k (by omega)).1.2
    rw [nbeq_false (Nat.pos_iff_ne_zero.1 hk0), nbeq_false (by omega : Nat.succ k ≠ cap)] at h1
    rw [hsplit, hsplit]
    exact lt_of_blt h1
  · intro k hk g hg
    have h1 := allR_spec (hd k hk).2.1 g hg
    simp only [andB_eq, orB_eq3, Bool.and_eq_true, Bool.or_eq_true] at h1
    rcases h1.1.2 with h2 | h2
    · exact Or.inl (Nat.eq_of_beq_eq_true h2)
    · right
      rw [hsplit]
      have := Nat.le_of_ble_eq_true h2
      change getN 0 P _ ≤ 16 * k + g at this
      omega

theorem x0ConjT_ok : oOrbOK x0CStep 16 (x0Eta 178) x0ConjT 84 = true ∧
    x0ConjT.mats.toList.map encR = (List.range 84).map (getN one CT) ∧
    ∀ X ∈ x0ConjT.mats.toList, WfA X :=
  xconj_ok (bits := 8) rfl (by decide) (by decide) (by decide) CTC.all

theorem x0ConjZ_ok : oOrbOK x0CStep 16 (x0Eta 407) x0ConjZ 7 = true ∧
    x0ConjZ.mats.toList.map encR = (List.range 7).map (getN one CZ) ∧
    ∀ X ∈ x0ConjZ.mats.toList, WfA X :=
  xconj_ok (bits := 5) rfl (by decide) (by decide) (by decide) CZC.all

end CertificateChecks.KernelJ4Q

end
