module

public import Certificates.Data.Kernel.Sp48L.Check

public section

namespace CertificateChecks.KernelSp48L

open CFSG.AGLEmbedding.KFactProofs.Sp48 CFSG.KC.Sp48L

theorem gens_k : gensValid = true := by decide +kernel

theorem r1_k : ceqP (powP t1c 9) oneP = true := by decide +kernel

theorem r2_k : ceqP (powP t2c 9) oneP = true := by decide +kernel

theorem r3_k : ceqP (powP fc 3) oneP = true := by decide +kernel

theorem r4_k : ceqP (powP t1c 3) oneP = false := by decide +kernel

theorem r5_k : ceqP (mulP t1c t2c) (mulP t2c t1c) = true := by decide +kernel

theorem r6_k : ceqP (mulP fc t1c) (mulP (powP t1c 7) fc) = true := by decide +kernel

theorem r7_k : ceqP (mulP fc t2c) (mulP (powP t2c 7) fc) = true := by decide +kernel

theorem r8_k : ceqP (mulP wc wc) oneP = true := by decide +kernel

theorem r9_k : ceqP (mulP sc sc) oneP = true := by decide +kernel

theorem r10_k : ceqP (mulP (mulP wc t1c) wc) (powP t1c 8) = true := by decide +kernel

theorem r11_k : ceqP (mulP wc t2c) (mulP t2c wc) = true := by decide +kernel

theorem r12_k : ceqP (mulP wc fc) (mulP fc wc) = true := by decide +kernel

theorem r13_k : ceqP (mulP (mulP sc t1c) sc) t2c = true := by decide +kernel

theorem r14_k : ceqP (mulP (mulP sc t2c) sc) t1c = true := by decide +kernel

theorem r15_k : ceqP (mulP sc fc) (mulP fc sc) = true := by decide +kernel

theorem hom_k : homK = true := by decide +kernel

end CertificateChecks.KernelSp48L
