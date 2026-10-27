module

public import Certificates.Data.Kernel.S5Ext.Check
public import Certificates.Kernel.S5Ext.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.S5Ext

theorem ch271071_cmp : cmpB CMP = true := by quickRfl

theorem ch271071_enum : eqL (enumA' CMP invsL) autK = true := by quickRfl

theorem ch271071_pack : packB 20 autK AKP = true := by quickRfl

theorem ch271071_sort : sortB autK 1048576 = true := by quickRfl

theorem ch271071_len : Nat.beq (lenL autK) 1152 = true := by quickRfl

theorem ch271071_ide : Nat.beq (l20 AKP IDE) IDK = true := by quickRfl

theorem ch271071_sg : (homT SG0 && homT SG1) = true := by quickRfl

theorem ch271071_tree : treeOK SG0 SG1 AKP IDE 1152 tree = true := by quickRfl

theorem ch271071_el0 : elB ELP KEYL 0 32 = true := by quickRfl

theorem ch271071_el1 : elB ELP KEYL 32 32 = true := by quickRfl

theorem ch271071_el2 : elB ELP KEYL 64 32 = true := by quickRfl

theorem ch271071_el3 : elB ELP KEYL 96 32 = true := by quickRfl

theorem ch271071_inc : incB KEYL 127 = true := by quickRfl

theorem ch271071_rows0 : rowsM MP ELP KEYL 0 32 = true := by quickRfl

theorem ch271071_rows1 : rowsM MP ELP KEYL 32 32 = true := by quickRfl

theorem ch271071_rows2 : rowsM MP ELP KEYL 64 32 = true := by quickRfl

theorem ch271071_rows3 : rowsM MP ELP KEYL 96 32 = true := by quickRfl

theorem ch271071_inv : invB MP INVP LIDE KEYL = true := by quickRfl

theorem ch271071_sq : sqB MP SQP = true := by quickRfl

theorem ch271071_ci : ciB ELP CIL = true := by quickRfl

theorem ch271071_bnd : bndB CATP 576 = true := by quickRfl

theorem ch271071_one : Nat.beq (lC CATP ONEK) (1 <<< LIDE) = true := by quickRfl

theorem ch271071_r0 : recsB MP INVP SQP CATP 0 r0 = true := by quickRfl
theorem ch271071_r1 : recsB MP INVP SQP CATP 32 r1 = true := by quickRfl
theorem ch271071_r2 : recsB MP INVP SQP CATP 64 r2 = true := by quickRfl
theorem ch271071_r3 : recsB MP INVP SQP CATP 96 r3 = true := by quickRfl
theorem ch271071_r4 : recsB MP INVP SQP CATP 128 r4 = true := by quickRfl
theorem ch271071_r5 : recsB MP INVP SQP CATP 160 r5 = true := by quickRfl
theorem ch271071_r6 : recsB MP INVP SQP CATP 192 r6 = true := by quickRfl
theorem ch271071_r7 : recsB MP INVP SQP CATP 224 r7 = true := by quickRfl
theorem ch271071_r8 : recsB MP INVP SQP CATP 256 r8 = true := by quickRfl
theorem ch271071_r9 : recsB MP INVP SQP CATP 288 r9 = true := by quickRfl
theorem ch271071_r10 : recsB MP INVP SQP CATP 320 r10 = true := by quickRfl
theorem ch271071_r11 : recsB MP INVP SQP CATP 352 r11 = true := by quickRfl
theorem ch271071_r12 : recsB MP INVP SQP CATP 384 r12 = true := by quickRfl
theorem ch271071_r13 : recsB MP INVP SQP CATP 416 r13 = true := by quickRfl
theorem ch271071_r14 : recsB MP INVP SQP CATP 448 r14 = true := by quickRfl
theorem ch271071_r15 : recsB MP INVP SQP CATP 480 r15 = true := by quickRfl
theorem ch271071_r16 : recsB MP INVP SQP CATP 512 r16 = true := by quickRfl
theorem ch271071_r17 : recsB MP INVP SQP CATP 544 r17 = true := by quickRfl

theorem ch271071_w0 : witsB MP ELP CIL CATP 0 w0 = true := by quickRfl
theorem ch271071_w1 : witsB MP ELP CIL CATP 32 w1 = true := by quickRfl
theorem ch271071_w2 : witsB MP ELP CIL CATP 64 w2 = true := by quickRfl
theorem ch271071_w3 : witsB MP ELP CIL CATP 96 w3 = true := by quickRfl
theorem ch271071_w4 : witsB MP ELP CIL CATP 128 w4 = true := by quickRfl
theorem ch271071_w5 : witsB MP ELP CIL CATP 160 w5 = true := by quickRfl
theorem ch271071_w6 : witsB MP ELP CIL CATP 192 w6 = true := by quickRfl
theorem ch271071_w7 : witsB MP ELP CIL CATP 224 w7 = true := by quickRfl
theorem ch271071_w8 : witsB MP ELP CIL CATP 256 w8 = true := by quickRfl
theorem ch271071_w9 : witsB MP ELP CIL CATP 288 w9 = true := by quickRfl
theorem ch271071_w10 : witsB MP ELP CIL CATP 320 w10 = true := by quickRfl
theorem ch271071_w11 : witsB MP ELP CIL CATP 352 w11 = true := by quickRfl
theorem ch271071_w12 : witsB MP ELP CIL CATP 384 w12 = true := by quickRfl
theorem ch271071_w13 : witsB MP ELP CIL CATP 416 w13 = true := by quickRfl
theorem ch271071_w14 : witsB MP ELP CIL CATP 448 w14 = true := by quickRfl
theorem ch271071_w15 : witsB MP ELP CIL CATP 480 w15 = true := by quickRfl
theorem ch271071_w16 : witsB MP ELP CIL CATP 512 w16 = true := by quickRfl
theorem ch271071_w17 : witsB MP ELP CIL CATP 544 w17 = true := by quickRfl

end CFSG.KD.S5Ext
