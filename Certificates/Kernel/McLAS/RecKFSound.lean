module

public import Certificates.Data.Kernel.McLAS.RecKF
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.McLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PF CFSG.KC.BfsPin

theorem bAnd_rot3 (a b c r : Bool) : bAnd(a, bAnd(b, bAnd(c, r))) = bAnd(c, bAnd(a, bAnd(b, r))) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem pairSelKF_eq (a x : Nat) : pairSelKF a x = pairSelK a x := by
  unfold pairSelKF pairSelK
  exact (bAnd_rot3 _ _ _ _).symm

theorem pcomp_pidn {n w t : Nat} (ht : canonK n w (mask w) (n * w) t = true) :
    pcomp n w (mask w) (pidn n w) t = t := by
  obtain ⟨hn, hw, hs, hlt⟩ := canon_facts ht
  have hn' : n < 2 ^ 32 := lt_of_lt_of_le hn (by norm_num)
  exact eq_of_fields (w_pos hw) (pcomp_shr _ _ hn' (w_pos hw)) hs fun i hi => by
    rw [pg_pcomp hn' hi, pg_pidn hn hw (hlt i hi)]

theorem stepK_id {n w k j t : Nat} {G GI : Nat → Nat} (hG : ∀ j < k, G j = pidn n w) (hj : j < k)
    (ht : canonK n w (mask w) (n * w) t = true) :
    stepK n w (mask w) true G GI j t = pcomp n w (mask w) t (GI j) := by
  unfold stepK
  rw [hG j hj]
  change pcomp n w (mask w) (pcomp n w (mask w) (pidn n w) t) (GI j) = _
  rw [pcomp_pidn ht]

theorem bIf_imp {c X Y : Bool} (hX : X = true → Y = true) (h : bIf(c, true, X) = true) :
    bIf(c, true, Y) = true := by
  cases c
  · exact hX h
  · rfl

theorem penumPtKF_parts {n w nw k cnt i : Nat} {GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtKF n w (mask w) nw GI k cnt T PL POS SRT SRI i = true) :
    canonK n w (mask w) nw (T i) = true ∧
    bIf(Nat.beq i (nat_lit 0), true,
      bAnd(Nat.blt (parOf PL i) i, bAnd(Nat.blt (labOf PL i) k,
        bAnd(Nat.beq (r32 POS (Nat.add (Nat.mul (parOf PL i) k) (labOf PL i))) i,
        bIf(Nat.blt (Nat.succ i) cnt,
          lexLtK (parOf PL i) (labOf PL i) (parOf PL (Nat.succ i)) (labOf PL (Nat.succ i)),
          true))))) = true ∧
    (∀ j < k, bAnd(Nat.blt (r32 POS (Nat.add (Nat.mul i k) j)) cnt,
      bAnd(Nat.beq (T (r32 POS (Nat.add (Nat.mul i k) j))) (pcomp n w (mask w) (T i) (GI j)),
      bIf(Nat.beq (r32 POS (Nat.add (Nat.mul i k) j)) (nat_lit 0), true,
        bIf(lexLtK i j (parOf PL (r32 POS (Nat.add (Nat.mul i k) j)))
          (labOf PL (r32 POS (Nat.add (Nat.mul i k) j))), false, true)))) = true) ∧
    bAnd(Nat.blt (r32 SRT i) cnt, bAnd(Nat.beq (r32 SRI (r32 SRT i)) i,
      bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (T (r32 SRT i)) (T (r32 SRT (Nat.succ i))), true))) =
      true := by
  unfold penumPtKF at h
  simp only [strictB_app'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
  exact ⟨h1, h3, fun j hj => allN_spec h5 j hj, h6⟩

theorem penumPtK_of_F {n w k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hG : ∀ j < k, G j = pidn n w)
    (hF : ∀ i < cnt, penumPtKF n w (mask w) (n * w) GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true := by
  intro i hi
  obtain ⟨hc, hpar, hpos, hsrt⟩ := penumPtKF_parts (hF i hi)
  unfold penumPtK
  simp only [strictB_app']
  refine (bAnd_iff _ _).2 ⟨hc, (bAnd_iff _ _).2 ⟨?_, (bAnd_iff _ _).2 ⟨?_, hsrt⟩⟩⟩
  · refine bIf_imp (fun hpar' => ?_) hpar
    · obtain ⟨a1, r1⟩ := (bAnd_iff _ _).1 hpar'
      obtain ⟨a2, r2⟩ := (bAnd_iff _ _).1 r1
      obtain ⟨a3, a4⟩ := (bAnd_iff _ _).1 r2
      have hp : parOf PL i < i := Nat.le_of_ble_eq_true a1
      have hl : labOf PL i < k := Nat.le_of_ble_eq_true a2
      obtain ⟨hcp, -, hposp, -⟩ := penumPtKF_parts (hF (parOf PL i) (by omega))
      have hq := hposp (labOf PL i) hl
      rw [Nat.eq_of_beq_eq_true a3] at hq
      obtain ⟨-, hq2⟩ := (bAnd_iff _ _).1 hq
      obtain ⟨hT, -⟩ := (bAnd_iff _ _).1 hq2
      refine (bAnd_iff _ _).2 ⟨a1, (bAnd_iff _ _).2 ⟨a2, (bAnd_iff _ _).2 ⟨?_, a4⟩⟩⟩
      rw [stepK_id hG hl hcp]
      exact hT
  · refine allN_of_forall fun j hj => ?_
    rw [stepK_id hG hj hc]
    exact hpos j hj

end CFSG.KS.McLAS

end
