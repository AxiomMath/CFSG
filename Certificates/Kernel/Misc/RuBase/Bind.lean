module

public import Certificates.Kernel.Misc.RuBase.Gens
public import Certificates.Kernel.Misc.RuSq.Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false
set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.RuBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelMisc.RuSq CertificateChecks.KernelMisc.TextBlocks

theorem asciiB42 : asciiBlocks 42 (3 * 4060 + 1) RuSqT.chars = true := by
  quickRfl

theorem line2 : lineK 3 4060 12 CD.n0 (RuSqT.chars.drop (2 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem line3 : lineK 3 4060 12 CD.n1 (RuSqT.chars.drop (3 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem line39 : lineK 3 4060 12 LD.n0 (RuSqT.chars.drop (39 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem line40 : lineK 3 4060 12 LD.n1 (RuSqT.chars.drop (40 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem line41 : lineK 3 4060 12 LD.n2 (RuSqT.chars.drop (41 * (3 * 4060 + 1))) = true := by
  quickRfl

theorem row_eq {j P : Nat} (hj : j < 42)
    (hk : lineK 3 4060 12 P (RuSqT.chars.drop (j * (3 * 4060 + 1))) = true) :
    ruArr4060 j = unpack 4060 12 P := by
  have ha : asciiK (RuSqT.chars.take ((j + 1) * (3 * 4060 + 1))) = true :=
    asciiK_take (by omega) (asciiBlocks_spec asciiB42)
  have hl := lineK_sound ha hk
  unfold ruArr4060 ruHexRow ruBytes4060 ruHexAt
  rw [RuSqT.eq]
  apply Array.ext
  · simp [CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact hl i (by simpa using h1)

theorem field_eq {f j : Nat} (hj : j < (ruLines4060.getD f (0, 0)).2) :
    (ruField4060 f)[j]! = ruArr4060 ((ruLines4060.getD f (0, 0)).1 + j) := by
  rw [ruField4060, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem rowC : ∀ l < 2, [(ruField4060 1)[0]!, (ruField4060 1)[1]!][l]! = unpack 4060 12 (GC l) := by
  intro l hl
  interval_cases l
  · exact (field_eq (f := 1) (j := 0) (by decide)).trans (row_eq (j := 2) (by omega) line2)
  · exact (field_eq (f := 1) (j := 1) (by decide)).trans (row_eq (j := 3) (by omega) line3)

theorem rowL : ∀ l < 3, [(ruField4060 5)[0]!, (ruField4060 5)[1]!, (ruField4060 5)[2]!][l]! =
    unpack 4060 12 (GL l) := by
  intro l hl
  interval_cases l
  · exact (field_eq (f := 5) (j := 0) (by decide)).trans (row_eq (j := 39) (by omega) line39)
  · exact (field_eq (f := 5) (j := 1) (by decide)).trans (row_eq (j := 40) (by omega) line40)
  · exact (field_eq (f := 5) (j := 2) (by decide)).trans (row_eq (j := 41) (by omega) line41)

end CertificateChecks.KernelMisc.RuBase

end
