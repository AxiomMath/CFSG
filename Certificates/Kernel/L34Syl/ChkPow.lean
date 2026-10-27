module

public import Certificates.Kernel.L34Syl.Data

public section

namespace CertificateChecks.KernelL34Syl

open CFSG.KC.L34Syl

theorem ch465003_lp : lettersOK 42 6 63 252 (lane 252 pm252 LP) 2 = true := by decide +kernel

theorem ch465003_ls : lettersOK 42 6 63 252 (lane 252 pm252 LS) 3 = true := by decide +kernel

theorem ch465003_lz : lettersOK 42 6 63 252 (lane 252 pm252 LZ) 3 = true := by decide +kernel

theorem ch465003_p : grpK 42 6 63 252 pm252 9 511 (lane 252 pm252 LP) 2 PT PD 9 = true := by
  decide +kernel

theorem ch465003_pow5 : powsK 42 6 63 252 pm252 5 RT5 224 = true := by decide +kernel

theorem ch465003_pow7 : powsK 42 6 63 252 pm252 7 RT7 112 = true := by decide +kernel

theorem ch465003_row5 : rowsK 42 6 63 252 pm252 5 7 LP RT5 TG ROW5 0 = true := by decide +kernel

theorem ch465003_row7 : rowsK 42 6 63 252 pm252 7 1 LP RT7 TG ROW7 0 = true := by decide +kernel

theorem ch465003_mem5 :
    wordsK 42 6 63 6 (lane 252 pm252 LS) (fun i => lane 252 pm252 RT5 (Nat.mul 4 i)) MEM5 0 =
      true := by
  decide +kernel

theorem ch465003_mem7 :
    wordsK 42 6 63 6 (lane 252 pm252 LS) (fun i => lane 252 pm252 RT7 (Nat.mul 6 i)) MEM7 0 =
      true := by
  decide +kernel

theorem ch465003_ps :
    wordsK 42 6 63 6 (lane 252 pm252 LS) (fun i => lane 252 pm252 LP (Nat.mul 2 i)) PS 0 = true := by
  decide +kernel

theorem ch465003_rs :
    wordsK 42 6 63 6 (lane 252 pm252 LS) (fun i => lane 252 pm252 TG (Nat.succ i)) RS 0 = true := by
  decide +kernel

theorem ch465003_zw :
    wordsK 42 6 63 6 (lane 252 pm252 LZ) (fun i => lane 252 pm252 LS (Nat.mul 2 i)) ZW 0 = true := by
  decide +kernel

end CertificateChecks.KernelL34Syl

end
