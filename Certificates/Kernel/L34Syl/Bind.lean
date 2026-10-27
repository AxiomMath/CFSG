module

public import Certificates.Kernel.L34Syl.Data
public import Certificates.Data.Kernel.L34Syl.TabEq
public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroupData

public section

namespace CertificateChecks.KernelL34Syl

open CFSG.KC.L34Syl CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native

theorem ch465003_bp : tabEqB pT (lane 252 pm252 LP 0) = true := by decide +kernel
theorem ch465003_bq : tabEqB qT (lane 252 pm252 LP 2) = true := by decide +kernel
theorem ch465003_bs0 : tabEqB gensS[0]! (lane 252 pm252 LS 0) = true := by decide +kernel
theorem ch465003_bs1 : tabEqB gensS[1]! (lane 252 pm252 LS 2) = true := by decide +kernel
theorem ch465003_bs2 : tabEqB gensS[2]! (lane 252 pm252 LS 4) = true := by decide +kernel
theorem ch465003_bm0 : tabEqB mRs[0]! (lane 252 pm252 TG 1) = true := by decide +kernel
theorem ch465003_bm1 : tabEqB mRs[1]! (lane 252 pm252 TG 2) = true := by decide +kernel
theorem ch465003_bm2 : tabEqB mRs[2]! (lane 252 pm252 TG 3) = true := by decide +kernel
theorem ch465003_bm3 : tabEqB mRs[3]! (lane 252 pm252 TG 4) = true := by decide +kernel
theorem ch465003_bm4 : tabEqB mRs[4]! (lane 252 pm252 TG 5) = true := by decide +kernel
theorem ch465003_bm5 : tabEqB mRs[5]! (lane 252 pm252 TG 6) = true := by decide +kernel

theorem ch465003_ez : lane 252 pm252 LZ 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LZ 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LZ 4 = lane 252 pm252 TG 0 := by
  decide +kernel

theorem ch465003_em0 : lane 252 pm252 LM0 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LM0 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LM0 4 = lane 252 pm252 TG 1 := by
  decide +kernel
theorem ch465003_em1 : lane 252 pm252 LM1 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LM1 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LM1 4 = lane 252 pm252 TG 2 := by
  decide +kernel
theorem ch465003_em2 : lane 252 pm252 LM2 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LM2 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LM2 4 = lane 252 pm252 TG 3 := by
  decide +kernel
theorem ch465003_em3 : lane 252 pm252 LM3 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LM3 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LM3 4 = lane 252 pm252 TG 4 := by
  decide +kernel
theorem ch465003_em4 : lane 252 pm252 LM4 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LM4 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LM4 4 = lane 252 pm252 TG 5 := by
  decide +kernel
theorem ch465003_em5 : lane 252 pm252 LM5 0 = lane 252 pm252 LP 0 ∧
    lane 252 pm252 LM5 2 = lane 252 pm252 LP 2 ∧ lane 252 pm252 LM5 4 = lane 252 pm252 TG 6 := by
  decide +kernel

theorem ch465003_len : MEM5.length = 224 ∧ MEM7.length = 112 ∧ ROW5.length = 224 ∧
    ROW7.length = 112 ∧ PS.length = 2 ∧ RS.length = 6 ∧ ZW.length = 3 ∧ REC5A.length = 504 ∧
    REC5B.length = 504 ∧ REC5C.length = 504 ∧ REC5D.length = 504 ∧ REC7A.length = 480 ∧
    REC7B.length = 480 ∧ CW0.length = 3 ∧ CW1.length = 3 ∧ CW2.length = 3 ∧ CW3.length = 3 ∧
    CW4.length = 3 ∧ CW5.length = 3 := by
  decide +kernel

@[expose] def cnOK (CN : Nat) : Prop :=
  CN % 256 = 1 ∧ (((CN / 256) % 256 = 10 ∧ (CN / 65536) % 256 = 45) ∨
    ((CN / 256) % 256 = 45 ∧ (CN / 65536) % 256 = 10))

theorem ch465003_cn : cnOK CN0 ∧ cnOK CN1 ∧ cnOK CN2 ∧ cnOK CN3 ∧ cnOK CN4 ∧ cnOK CN5 := by
  unfold cnOK
  decide +kernel

end CertificateChecks.KernelL34Syl

end
