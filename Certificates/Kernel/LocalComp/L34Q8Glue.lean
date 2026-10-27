module

public import Certificates.Kernel.LocalComp.L34Q8Chk
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KD.L34Q8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.PSL3Four.Native
  CFSG.EvenSporadicStandard.L34Q8 CFSG.Monster.B.Co2.Native

theorem size_unpack42 (p : Nat) : (unpack 42 6 p).size = 42 := by simp [unpack]

theorem q8OK_ok : q8OK = true := by
  have hb := bindQ8_ok
  simp only [bindQ8, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, b1⟩, b2⟩, b3⟩, b5⟩, b6⟩, q1⟩, q2⟩, q3⟩, q5⟩, q6⟩ := hb
  have e1 := unpack_eq_of_bindArrK b1
  have e2 := unpack_eq_of_bindArrK b2
  have e3 := unpack_eq_of_bindArrK b3
  have e5 := unpack_eq_of_bindArrK b5
  have e6 := unpack_eq_of_bindArrK b6
  have c1 := (PP_of_permOK hsz q1).1
  have c2 := (PP_of_permOK hsz q2).1
  have c3 := (PP_of_permOK hsz q3).1
  have c5 := (PP_of_permOK hsz q5).1
  have c6 := (PP_of_permOK hsz q6).1
  have ci1 := (PP_of_permOK hsz q1).inv.1
  have ci2 := (PP_of_permOK hsz q2).inv.1
  have ci3 := (PP_of_permOK hsz q3).inv.1
  have cid := (PP.id hsz).1
  have hid : idTab 42 = unpack 42 6 (pidn 42 6) := idA_eq hsz
  have i1 : invTab 42 (unpack 42 6 P1) = unpack 42 6 (pi P1) := invCand_unpack q1
  have i2 : invTab 42 (unpack 42 6 P2) = unpack 42 6 (pi P2) := invCand_unpack q2
  have i3 : invTab 42 (unpack 42 6 P3) = unpack 42 6 (pi P3) := invCand_unpack q3
  have hLT : letterTabs = #[unpack 42 6 P1, unpack 42 6 P2, unpack 42 6 P3, unpack 42 6 (pi P1),
      unpack 42 6 (pi P2), unpack 42 6 (pi P3)] := by
    unfold letterTabs
    rw [e1, e2, e3, i1, i2, i3]
  have hG : ∀ j < 6, letterTabs[j]! = unpack 42 6 (LQ j) := by
    intro j hj
    rw [hLT]
    interval_cases j <;> simp [LQ]
  have hGc : ∀ j < 6, canonK 42 6 (mask 6) (42 * 6) (LQ j) = true := by
    intro j hj
    interval_cases j <;> simp only [LQ, List.getD_cons_zero, List.getD_cons_succ]
    exacts [c1, c2, c3, ci1, ci2, ci3]
  have hw : ∀ wd : List Nat, (∀ j ∈ wd, j < 6) →
      wordT wd = unpack 42 6 (wK wd) ∧ canonK 42 6 (mask 6) (42 * 6) (wK wd) = true :=
    fun wd h => ⟨CFSG.KC.PermTool.wordTabS_unpack cid hid wd (fun j hj => hGc j (h j hj))
      (fun j hj => hG j (h j hj)),
      CFSG.KC.PermTool.canonK_wordTabK cid wd (fun j hj => hGc j (h j hj))⟩
  obtain ⟨wx1, cx1⟩ := hw wX1 (by decide)
  obtain ⟨wy1, cy1⟩ := hw wY1 (by decide)
  obtain ⟨wx4, cx4⟩ := hw wX4 (by decide)
  obtain ⟨wy4, cy4⟩ := hw wY4 (by decide)
  have mul : ∀ {p q : Nat}, canonK 42 6 (mask 6) (42 * 6) p = true →
      canonK 42 6 (mask 6) (42 * 6) q = true →
      comp 42 (unpack 42 6 p) (unpack 42 6 q) = unpack 42 6 (pc p q) ∧
        canonK 42 6 (mask 6) (42 * 6) (pc p q) = true :=
    fun hp hq => ⟨compA_unpack hp hq, canonK_pcomp hp hq⟩
  have beq : ∀ {p q : Nat}, canonK 42 6 (mask 6) (42 * 6) p = true →
      canonK 42 6 (mask 6) (42 * 6) q = true →
      (unpack 42 6 p == unpack 42 6 q) = Nat.beq p q :=
    fun hp hq => CFSG.KC.L34KSnd.beq_unpack hp hq
  have hinv : inverseLettersOK = true := by
    have hk := q8K_ok
    simp only [q8K, Bool.and_eq_true] at hk
    unfold inverseLettersOK allBelow
    rw [List.all_eq_true]
    intro j hj
    have hj3 : j < 3 := List.mem_range.1 hj
    have ca := hGc (j + 3) (by omega)
    have cb := hGc j (by omega)
    rw [hG (j + 3) (by omega), hG j (by omega), size_unpack42, (mul ca cb).1, hid,
      beq (mul ca cb).2 cid]
    interval_cases j
    · simpa using hk.1.1.1.1
    · simpa using hk.1.1.1.2
    · simpa using hk.1.1.2
  have hk := q8K_ok
  simp only [q8K, Bool.and_eq_true] at hk
  obtain ⟨⟨-, ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩⟩, ⟨⟨⟨⟨k5, k6⟩, k7⟩, k8⟩, k9⟩⟩ := hk
  obtain ⟨m11, n11⟩ := mul c1 c1
  obtain ⟨m112, n112⟩ := mul n11 c2
  obtain ⟨m1121, n1121⟩ := mul n112 c1
  obtain ⟨m56, n56⟩ := mul c5 c6
  have hr1 : r₁T = unpack 42 6 (pc (pc (pc P1 P1) P2) P1) := by
    unfold r₁T
    rw [e1, e2, m11, m112, m1121]
  have hr4 : r₄T = unpack 42 6 (pc P5 P6) := by
    unfold r₄T
    rw [e5, e6, m56]
  have hc1 : class1OK = true := by
    simp only [class1OK]
    obtain ⟨mxx, nxx⟩ := mul cx1 cx1
    obtain ⟨myy, nyy⟩ := mul cy1 cy1
    obtain ⟨mxy, nxy⟩ := mul cx1 cy1
    obtain ⟨mxyx, nxyx⟩ := mul nxy cx1
    rw [wx1, wy1, hr1, hid, mxx, myy, mxy, mxyx, beq nxx n1121, beq nyy n1121, beq n1121 cid,
      beq nxyx cy1, k1, k2, k3, k4]
    rfl
  have hc4 : class4OK = true := by
    simp only [class4OK]
    obtain ⟨mxx, nxx⟩ := mul cx4 cx4
    obtain ⟨myy, nyy⟩ := mul cy4 cy4
    obtain ⟨mxy, nxy⟩ := mul cx4 cy4
    obtain ⟨mxyx, nxyx⟩ := mul nxy cx4
    obtain ⟨mxr, nxr⟩ := mul cx4 n56
    obtain ⟨mrx, nrx⟩ := mul n56 cx4
    obtain ⟨myr, nyr⟩ := mul cy4 n56
    obtain ⟨mry, nry⟩ := mul n56 cy4
    rw [wx4, wy4, hr4, hid, mxx, myy, mxy, mxyx, mxr, mrx, myr, mry, beq nxx nyy, beq nxx cid,
      beq nxyx cy4, beq nxr nrx, beq nyr nry, k5, k6, k7, k8, k9]
    rfl
  unfold q8OK
  rw [hinv, hc1, hc4]
  rfl

end CFSG.KD.L34Q8

end
