module

public import CFSG.Quasithin.Background.H47WChk64
public import Certificates.Kernel.L34M64.Glue
public import Certificates.Kernel.L34M64.Four

public section

namespace CertificateChecks.KernelL34M64

open CFSG.KC.L34M64 CFSG.KD.L34M64 CFSG.Quasithin.H13.Ch9.L34M CFSG.KC.HMathieu

theorem rankOKK_eq : rankOKK = rankOK := by
  funext r n cs ws
  simp only [rankOKK, rankOK, actK_fun]

theorem four_of (L : List (List ℕ × List ℕ))
    (h : (L.all fun d => AllLt 64 d.1 && rankOKK 4 64 d.1 (pickWitK 64 4 d.1)) = true) :
    ((L.map fun d => (d.1, pickWit 64 4 d.1)).all fun d => AllLt 64 d.1 && rankOK 4 64 d.1 d.2) =
      true := by
  simpa only [List.all_map, Function.comp_def, rankOKK_eq, pickWitK_eq] using h

theorem chk64four_true : CFSG.Quasithin.H47W.chk64four = true := by
  rw [CFSG.Quasithin.H47W.chk64four, CFSG.Quasithin.H47W.dat64four, dat_eq]
  exact four_of DAT ch7258four

end CertificateChecks.KernelL34M64
