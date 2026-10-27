module

public import CFSG.Quasithin.H13.L32N1447Inputs
public import Certificates.Kernel.H13.Q1447
public import Certificates.Kernel.H13.Q1447K
public import Certificates.Kernel.H13.ElemsS7
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.Q1447Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000 in
theorem s7L_length : D.s7L.length = 5040 := by decide +kernel

theorem kbX_unpackM (p : ℕ) : kbX (unpackM p) = kbY p := by
  rw [kbX, kbY, pow8_beq_one, hs_contains_toLR, elemsOf_toF]

set_option maxRecDepth 100000 in
theorem q1447_s7KB_true : s7KB = true := by
  rw [s7KB_split, q1447_kbHead_true, Bool.true_and, s7E_eq, List.all_map, Function.comp_def]
  simp only [kbX_unpackM]
  apply CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 240 21 (by rw [s7L_length])
  intro j hj
  interval_cases j
  · exact kbChunk0
  · exact kbChunk1
  · exact kbChunk2
  · exact kbChunk3
  · exact kbChunk4
  · exact kbChunk5
  · exact kbChunk6
  · exact kbChunk7
  · exact kbChunk8
  · exact kbChunk9
  · exact kbChunk10
  · exact kbChunk11
  · exact kbChunk12
  · exact kbChunk13
  · exact kbChunk14
  · exact kbChunk15
  · exact kbChunk16
  · exact kbChunk17
  · exact kbChunk18
  · exact kbChunk19
  · exact kbChunk20

theorem q1447Check_true : q1447Check = true := by
  simp only [q1447Check, List.all_cons, List.all_nil, q1447_s7InvB_true, q1447_g5InvB_true,
    q1447_m22InvB_true, q1447_o3InvB0, q1447_o3InvB1, q1447_s7KB_true, q1447_g5KB_true,
    q1447_m22KB_true, Bool.and_true]

end CertificateChecks.KernelH13

end
