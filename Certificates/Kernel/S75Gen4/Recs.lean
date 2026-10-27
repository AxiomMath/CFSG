module

public import Certificates.Data.Kernel.S75Gen4.Check
public import Certificates.Kernel.S75Gen4.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelS75Gen4

open CFSG.KD.S5Ext CFSG.KD.S75Gen4

theorem ch6132_r0 : recsB MP INVP SQP CATP 0 r0 = true := by quickRfl
theorem ch6132_r1 : recsB MP INVP SQP CATP 32 r1 = true := by quickRfl
theorem ch6132_r2 : recsB MP INVP SQP CATP 64 r2 = true := by quickRfl
theorem ch6132_r3 : recsB MP INVP SQP CATP 96 r3 = true := by quickRfl
theorem ch6132_r4 : recsB MP INVP SQP CATP 128 r4 = true := by quickRfl
theorem ch6132_r5 : recsB MP INVP SQP CATP 160 r5 = true := by quickRfl
theorem ch6132_r6 : recsB MP INVP SQP CATP 192 r6 = true := by quickRfl
theorem ch6132_r7 : recsB MP INVP SQP CATP 224 r7 = true := by quickRfl
theorem ch6132_r8 : recsB MP INVP SQP CATP 256 r8 = true := by quickRfl
theorem ch6132_r9 : recsB MP INVP SQP CATP 288 r9 = true := by quickRfl
theorem ch6132_r10 : recsB MP INVP SQP CATP 320 r10 = true := by quickRfl
theorem ch6132_r11 : recsB MP INVP SQP CATP 352 r11 = true := by quickRfl
theorem ch6132_r12 : recsB MP INVP SQP CATP 384 r12 = true := by quickRfl
theorem ch6132_r13 : recsB MP INVP SQP CATP 416 r13 = true := by quickRfl
theorem ch6132_r14 : recsB MP INVP SQP CATP 448 r14 = true := by quickRfl
theorem ch6132_r15 : recsB MP INVP SQP CATP 480 r15 = true := by quickRfl
theorem ch6132_r16 : recsB MP INVP SQP CATP 512 r16 = true := by quickRfl
theorem ch6132_r17 : recsB MP INVP SQP CATP 544 r17 = true := by quickRfl

theorem ch6132_q0 : genRecsB 10 TAB10 MP CATP 0 q0 = true := by quickRfl
theorem ch6132_q1 : genRecsB 10 TAB10 MP CATP 32 q1 = true := by quickRfl
theorem ch6132_q2 : genRecsB 10 TAB10 MP CATP 64 q2 = true := by quickRfl
theorem ch6132_q3 : genRecsB 10 TAB10 MP CATP 96 q3 = true := by quickRfl
theorem ch6132_q4 : genRecsB 10 TAB10 MP CATP 128 q4 = true := by quickRfl
theorem ch6132_q5 : genRecsB 10 TAB10 MP CATP 160 q5 = true := by quickRfl
theorem ch6132_q6 : genRecsB 10 TAB10 MP CATP 192 q6 = true := by quickRfl
theorem ch6132_q7 : genRecsB 10 TAB10 MP CATP 224 q7 = true := by quickRfl
theorem ch6132_q8 : genRecsB 10 TAB10 MP CATP 256 q8 = true := by quickRfl
theorem ch6132_q9 : genRecsB 10 TAB10 MP CATP 288 q9 = true := by quickRfl
theorem ch6132_q10 : genRecsB 10 TAB10 MP CATP 320 q10 = true := by quickRfl
theorem ch6132_q11 : genRecsB 10 TAB10 MP CATP 352 q11 = true := by quickRfl
theorem ch6132_q12 : genRecsB 10 TAB10 MP CATP 384 q12 = true := by quickRfl
theorem ch6132_q13 : genRecsB 10 TAB10 MP CATP 416 q13 = true := by quickRfl
theorem ch6132_q14 : genRecsB 10 TAB10 MP CATP 448 q14 = true := by quickRfl
theorem ch6132_q15 : genRecsB 10 TAB10 MP CATP 480 q15 = true := by quickRfl
theorem ch6132_q16 : genRecsB 10 TAB10 MP CATP 512 q16 = true := by quickRfl
theorem ch6132_q17 : genRecsB 10 TAB10 MP CATP 544 q17 = true := by quickRfl

theorem ch6132_d11 : genRecsB 11 TAB11 MP CATP 0 (q0 ++ q1 ++ q2 ++ q3 ++ q4 ++ q5 ++ q6 ++ q7 ++
    q8 ++ q9 ++ q10 ++ q11 ++ q12 ++ q13 ++ q14 ++ q15 ++ q16 ++ q17) = true := by quickRfl

end CertificateChecks.KernelS75Gen4

end
