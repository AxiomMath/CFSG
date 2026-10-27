module

public import CFSG.Certificates.Kernel.SporSch.Co1TernSound
public import CFSG.Sporadic.Schreier.Co1TernaryCodeInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Tern

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree CFSG.KS.SporSch.Tern Matrix

@[expose] def P : Nat := 5629748827378407714851890083668370772022613

@[expose] def C : List Nat := [1, 0, 0, 0, 0, 0, 264, 0, 0, 440, 0, 0, 24]

@[expose] def S : List Nat := [63, 221, 231, 250, 335, 374, 377, 414, 427, 437, 467, 492, 603, 622,
  629, 655, 691, 700, 726, 745, 791, 813, 826, 860, 867, 921, 934, 965, 970, 1008, 1118, 1133,
  1139, 1175, 1198, 1209, 1227, 1268, 1307, 1319, 1340, 1365, 1386, 1421, 1458, 1478, 1496,
  1505, 1565, 1579, 1590, 1607, 1656, 1690, 1701, 1740, 1745, 1762, 1806, 1841, 1865, 1874,
  1892, 1923, 1940, 1960, 2135, 2155, 2172, 2203, 2221, 2230, 2254, 2289, 2333, 2350, 2355,
  2394, 2405, 2439, 2488, 2505, 2516, 2530, 2590, 2599, 2617, 2637, 2674, 2709, 2730, 2755,
  2776, 2788, 2827, 2868, 2886, 2897, 2920, 2956, 2962, 2977, 3087, 3125, 3130, 3161, 3174,
  3228, 3235, 3269, 3282, 3304, 3350, 3369, 3395, 3404, 3440, 3466, 3473, 3492, 3603, 3628,
  3658, 3668, 3681, 3718, 3721, 3760, 3845, 3864, 3874, 4032]

theorem code : ternK Data.ternRows P C S = true := by quickRfl

theorem weights : ∀ n < 13,
    (Finset.univ.filter fun b : Fin 6 → ZMod 3 => (tsupp (b ᵥ* R)).card = n).card =
      weightCount n := by
  intro n hn
  unfold tsupp
  rw [(ternK_sound (Rm := R) rfl code).1 n hn]
  unfold weightCount C
  interval_cases n <;> rfl

theorem supports : sixSupports.card = 132 ∧
    ∀ F ∈ (Finset.univ : Finset (Fin 12)).powersetCard 5,
      (sixSupports.filter fun s => F ⊆ s).card = 1 :=
  ⟨(ternK_sound (Rm := R) rfl code).2.1, (ternK_sound (Rm := R) rfl code).2.2⟩

end CertificateChecks.KernelSporSch.Co1Tern

end
