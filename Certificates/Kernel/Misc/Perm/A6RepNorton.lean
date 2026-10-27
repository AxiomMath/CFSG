module

public import Certificates.Kernel.Misc.Perm.A6RepDefs

public section

namespace CertificateChecks.KernelMisc.A6Rep

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
open Equiv FieldFour

theorem hA : sumTerms (cert8a.terms.map fun p => (p.2, rep8aTab p.1)) = aT := by decide +kernel

theorem s_0 : rep8aTab cert8a.spin[0] = sT[0] := by decide +kernel

theorem s_1 : rep8aTab cert8a.spin[1] = sT[1] := by decide +kernel

theorem s_2 : rep8aTab cert8a.spin[2] = sT[2] := by decide +kernel

theorem s_3 : rep8aTab cert8a.spin[3] = sT[3] := by decide +kernel

theorem s_4 : rep8aTab cert8a.spin[4] = sT[4] := by decide +kernel

theorem s_5 : rep8aTab cert8a.spin[5] = sT[5] := by decide +kernel

theorem s_6 : rep8aTab cert8a.spin[6] = sT[6] := by decide +kernel

theorem s_7 : rep8aTab cert8a.spin[7] = sT[7] := by decide +kernel

theorem hS : cert8a.spin.map rep8aTab = sT := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map]
  interval_cases i
  · exact s_0
  · exact s_1
  · exact s_2
  · exact s_3
  · exact s_4
  · exact s_5
  · exact s_6
  · exact s_7

theorem d_0 : rep8aTab cert8a.dual[0] = dT[0] := by decide +kernel

theorem d_1 : rep8aTab cert8a.dual[1] = dT[1] := by decide +kernel

theorem d_2 : rep8aTab cert8a.dual[2] = dT[2] := by decide +kernel

theorem d_3 : rep8aTab cert8a.dual[3] = dT[3] := by decide +kernel

theorem d_4 : rep8aTab cert8a.dual[4] = dT[4] := by decide +kernel

theorem d_5 : rep8aTab cert8a.dual[5] = dT[5] := by decide +kernel

theorem d_6 : rep8aTab cert8a.dual[6] = dT[6] := by decide +kernel

theorem d_7 : rep8aTab cert8a.dual[7] = dT[7] := by decide +kernel

theorem hD : cert8a.dual.map rep8aTab = dT := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map]
  interval_cases i
  · exact d_0
  · exact d_1
  · exact d_2
  · exact d_3
  · exact d_4
  · exact d_5
  · exact d_6
  · exact d_7

theorem hC : cert8a.checkWith aT sT dT = true := by decide +kernel

theorem cert8aOK : cert8a.check rep8aTab = true := by
  unfold NortonData.check
  rw [hA, hS, hD]
  exact hC

end CertificateChecks.KernelMisc.A6Rep

end
