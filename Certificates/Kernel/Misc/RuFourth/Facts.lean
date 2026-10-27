module

public import Certificates.Kernel.Misc.RuFourth.Check
public import CFSG.Certificates.Kernel.Misc.RuFourthSound

public section

namespace CertificateChecks.KernelMisc.RuFourth

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KC.Misc.RuFourth
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.Bridge.SurjD.Native
  CertificateChecks.KernelMisc.TextBlocks

theorem entry_eq {k i : Nat} (hk : k < 3) (hi : i < 16240) :
    CFSG.Monster.B.Co2.Native.hexAt ruRhoText.toUTF8 (4 * (16240 * k + i)) 4 =
      pg 14 (mask 14) (RK k) i := by
  have hl : lineOK k = true := by
    interval_cases k
    exacts [line0, line1, line2]
  have ha : asciiK (RuFRT.chars.take (64960 * k + 4 * 16240)) = true :=
    asciiK_take (by omega) (asciiBlocks_spec asciiB)
  have h := CFSG.KC.Misc.RuFourth.lineK_sound_at ha hl i hi
  rw [hexAt_eq, RuFRT.eq]
  rw [show 4 * (16240 * k + i) = 64960 * k + 4 * i by omega]
  exact h

theorem rho_eq : ∀ k < 3,
    CFSG.Monster.B.Co2.Native.hexTable 4 16240 (16240 * k) ruRhoText = unpack 16240 14 (RK k) := by
  intro k hk
  apply Array.ext
  · simp [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    have hi : i < 16240 := by simpa [CFSG.Monster.B.Co2.Native.hexTable] using h1
    exact entry_eq hk hi

theorem p0_eq : (ruSpec ()).surjWords[0]! = intsK RuFST.chars := by
  have h := intsK_sound textS
  rw [← RuFST.eq] at h
  exact h

theorem permOKs : ∀ l < 3, permOK 16240 14 16383 (16240 * 14) (RK l) (RIK l) = true := by
  intro l hl
  interval_cases l
  exacts [perm0, perm1, perm2]

theorem w2OK : oneP RK RIK (intsK RuFST.chars)
    (wordFrom RK RIK [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3] idP) 48 0 = true := by
  have e : wordFrom RK RIK [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3] idP = X2 := by
    rw [show [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, (3 : Int)] =
      [-2, -1, -3, -1, -3, -1, 3] ++ [-2, -1, -3, -1, -3, -1, 3] from rfl, wordFrom_append,
      Nat.eq_of_beq_eq_true c1OK, Nat.eq_of_beq_eq_true x2OK]
  rw [e]
  exact w2X

end CertificateChecks.KernelMisc.RuFourth

end
