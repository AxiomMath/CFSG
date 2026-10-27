
module

public import Certificates.Kernel.SporSch.Th.Orb2315K
public import Certificates.Kernel.SporSch.Th.Plane2320Base
public import CFSG.Certificates.Kernel.SporSch.ThOrbSound

@[expose] public section

namespace CertificateChecks.KernelSporSch.ThOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native
open CFSG.Sporadic.ThSchreier (rowsLX rowsLY rowsT rowsVInv orbTable orbRows orbPar orbLab orbEdge
  conjRowsH orbitChecks centOrbitPar centOrbitLab centOrbitEdges transporterWord invWord abRows
  abLetterRows signedRows natsOf)
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThOrbK

theorem of_blocks {f : Nat → Bool} (h : ∀ q < 117, allBlk (Nat.mul q 7) f 7 = true) :
    ∀ i < 819, f i = true := by
  intro i hi
  have := allBlk_spec (h (i / 7) (by omega)) (i % 7) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul (i / 7) 7) (i % 7) = i := by
    rw [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod' i 7
  rwa [e] at this

theorem hent (i : Nat) (hi : i < 819) :
    ThO.SG i < 819 ∧ ThO.TU (ThO.SG i) = i ∧ (i = 0 → ThO.S (ThO.SG i) = ThO.T) ∧
      (i ≠ 0 → ThO.PAR i < i ∧ (ThO.LAB i = 1 ∨ ThO.LAB i = 2) ∧
        ThO.EDG (2 * ThO.PAR i + (ThO.LAB i - 1)) = i) ∧
      ThO.EDG (2 * i) < 819 ∧ ThO.EDG (2 * i + 1) < 819 ∧
      mulPk (mulPk ThO.X (ThO.S (ThO.SG i))) ThO.X = ThO.S (ThO.SG (ThO.EDG (2 * i))) ∧
      mulPk (mulPk ThO.Y (ThO.S (ThO.SG i))) ThO.YY = ThO.S (ThO.SG (ThO.EDG (2 * i + 1))) :=
  entK_spec (of_blocks ThO.hE i hi)

theorem hsrt (k : Nat) (hk : k < 819) :
    repk (unpk (ThO.S k)) = ThO.S k ∧ (k < 818 → ThO.S k < ThO.S (k + 1)) :=
  srtK_spec (of_blocks ThO.hS k hk)

theorem rowsA_eq : CFSG.Sporadic.Th.Max3.rowsA = rowsV (unpk ThO.A) := by
  rw [ThUA.rowsA_eq]
  exact ThPlane.rowsV_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec bA i hi)).symm

theorem rowsB_eq : CFSG.Sporadic.Th.Max3.rowsB = rowsV (unpk ThO.B) := by
  rw [ThPlane.rowsB_eq]
  exact ThPlane.rowsV_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec bB i hi)).symm

theorem rowsBB_eq : mulRows CFSG.Sporadic.Th.Max3.rowsB CFSG.Sporadic.Th.Max3.rowsB =
    rowsV (unpk ThO.BB) := by
  rw [rowsB_eq, mulPk_sound, Nat.eq_of_beq_eq_true bBB]

theorem letter (z : Int) : abLetterRows z = rowsV (unpk (letPk ThO.A ThO.B ThO.BB z)) := by
  rw [letPk_spec, abLetterRows]
  split_ifs
  · exact rowsA_eq
  · exact rowsB_eq
  · exact rowsBB_eq

theorem bind_of {R : Nat → Nat} {cs : List Char} {N : Nat}
    (h : Nat.beq (thBindK false R cs) (2 * N) = true) :
    ∀ t < N, (natsOf (String.ofList cs)).getD t 0 = R t := by
  have hb := Nat.eq_of_beq_eq_true h
  obtain ⟨hl0, hv0⟩ := thBind_sound (hex := false) (R := R) (cs := cs) (by rw [hb]; omega)
  have hl : (natsOf (String.ofList cs)).length = thBindK false R cs / 2 := hl0
  have hv : ∀ t < (natsOf (String.ofList cs)).length, (natsOf (String.ofList cs)).getD t 0 = R t :=
    hv0
  rw [hb] at hl
  intro t ht
  exact hv t (by omega)

theorem par_eq (i : Nat) (hi : i < 819) : orbPar i = ThO.PAR i := by
  rw [orbPar, ThPar.eq]
  exact bind_of bPar i hi

theorem lab_eq (i : Nat) (hi : i < 819) : orbLab i = ThO.LAB i := by
  rw [orbLab, ThLab.eq]
  exact bind_of bLab i hi

theorem edg_eq (t : Nat) (ht : t < 1638) : centOrbitEdges.getD t 0 = ThO.EDG t := by
  rw [ThEdg.eq]
  exact bind_of bEdg t ht

theorem edge1 (i : Nat) (hi : i < 819) : orbEdge i 1 = ThO.EDG (2 * i) := by
  rw [orbEdge, edg_eq _ (by omega)]
  rfl

theorem edge2 (i : Nat) (hi : i < 819) : orbEdge i 2 = ThO.EDG (2 * i + 1) := by
  rw [orbEdge, edg_eq _ (by omega)]

theorem s_lt : ∀ b, b < 819 → ∀ a < b, ThO.S a < ThO.S b := by
  intro b
  induction b with
  | zero => intro _ a ha; omega
  | succ b ih =>
    intro hb a ha
    have hs := (hsrt b (by omega)).2 (by omega)
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.lt_trans (ih (by omega) a h) hs
    · have : a = b := by omega
      rw [this]
      exact hs

theorem s_inj {a b : Nat} (ha : a < 819) (hb : b < 819) (h : ThO.S a = ThO.S b) : a = b := by
  rcases Nat.lt_trichotomy a b with l | e | g
  · exact absurd h (Nat.ne_of_lt (s_lt b hb a l))
  · exact e
  · exact absurd h.symm (Nat.ne_of_lt (s_lt a ha b g))

end CertificateChecks.KernelSporSch.ThOrb

end
