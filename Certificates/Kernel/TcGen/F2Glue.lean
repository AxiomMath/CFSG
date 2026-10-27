module

public import Certificates.Kernel.TcGen.F2
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint

theorem tc_of {d A B : Nat} (hd : 0 < d) {sA sB : String}
    (eA : (ops2 d).decode sA = CFSG.KC.Co1F2.unpackR d A)
    (eB : (ops2 d).decode sB = CFSG.KC.Co1F2.unpackR d B) {n : Nat} {prog : List Op}
    {D : TSpec} (hA : D.rA < n) (hB : D.rB < n) (hw : D.wf = true)
    (h : seedsF2 d A B n prog D.facts D.rA D.rB = true) :
    tcCheck (ops2 d) sA sB n prog D = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 d hd) eA eB trivial trivial (fs := D.facts) hA hB h
  unfold tcCheck
  rw [hm, h0, h1, decide_eq_true hA, decide_eq_true hB, hw]
  rfl

theorem cp_of {d A B : Nat} (hd : 0 < d) {sA sB : String}
    (eA : (ops2 d).decode sA = CFSG.KC.Co1F2.unpackR d A)
    (eB : (ops2 d).decode sB = CFSG.KC.Co1F2.unpackR d B) {n : Nat} {prog : List Op}
    {D : CpSpec} (hA : D.rA < n) (hB : D.rB < n) (hw : D.wf = true)
    (h : seedsF2 d A B n prog D.facts D.rA D.rB = true) :
    cpCheck (ops2 d) sA sB n prog D = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 d hd) eA eB trivial trivial (fs := D.facts) hA hB h
  unfold cpCheck
  rw [hm, h0, h1, decide_eq_true hA, decide_eq_true hB, hw]
  rfl

theorem c3A : (ops2 22).decode NativeSporadic.Co3Seed1 = CFSG.KC.Co1F2.unpackR 22 C3A.M := by
  rw [C3A.eq]
  exact CFSG.KC.Co1F2.bind_sound C3A.bind

theorem c3B : (ops2 22).decode NativeSporadic.Co3Seed2 = CFSG.KC.Co1F2.unpackR 22 C3B.M := by
  rw [C3B.eq]
  exact CFSG.KC.Co1F2.bind_sound C3B.bind

theorem c2A : (ops2 22).decode NativeSporadic.Co2Seed1 = CFSG.KC.Co1F2.unpackR 22 C2A.M := by
  rw [C2A.eq]
  exact CFSG.KC.Co1F2.bind_sound C2A.bind

theorem c2B : (ops2 22).decode NativeSporadic.Co2Seed2 = CFSG.KC.Co1F2.unpackR 22 C2B.M := by
  rw [C2B.eq]
  exact CFSG.KC.Co1F2.bind_sound C2B.bind

theorem c1A : (ops2 24).decode NativeSporadic.Co1Seed1 = CFSG.KC.Co1F2.unpackR 24 C1A.M := by
  rw [C1A.eq]
  exact CFSG.KC.Co1F2.bind_sound C1A.bind

theorem c1B : (ops2 24).decode NativeSporadic.Co1Seed2 = CFSG.KC.Co1F2.unpackR 24 C1B.M := by
  rw [C1B.eq]
  exact CFSG.KC.Co1F2.bind_sound C1B.bind

theorem cert9418 :
    (tcCheck (ops2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2 Co3Three.tcNregs
      Co3Three.tcProg Co3Three.tcSpec = true) ∧
    (cpCheck (ops2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2 Co3Three.cpNregs
      Co3Three.cpProg Co3Three.cpSpec = true) ∧ (Co3Three.cpSpec.noFun = true) :=
  ⟨tc_of (by norm_num) c3A c3B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co3tc_K,
    cp_of (by norm_num) c3A c3B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co3cp_K,
    by decide +kernel⟩

theorem cert9419 :
    (tcCheck (ops2 22) NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2 Co2Three.tcNregs
      Co2Three.tcProg Co2Three.tcSpec = true) ∧
    (cpCheck (ops2 22) NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2 Co2Three.cpNregs
      Co2Three.cpProg Co2Three.cpSpec = true) ∧ (Co2Three.cpSpec.noFun = true) :=
  ⟨tc_of (by norm_num) c2A c2B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co2tc_K,
    cp_of (by norm_num) c2A c2B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co2cp_K,
    by decide +kernel⟩

theorem cert9502 :
    (tcCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2 Co1Five.tcNregs
      Co1Five.tcProg Co1Five.tcSpec = true) ∧
    (cpCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2 Co1Five.cpNregs
      Co1Five.cpProg Co1Five.cpSpec = true) ∧ (Co1Five.cpSpec.noFun = true) :=
  ⟨tc_of (by norm_num) c1A c1B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co1ftc_K,
    cp_of (by norm_num) c1A c1B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co1fcp_K,
    by decide +kernel⟩

theorem cert9503 :
    (tcCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2 Co1Three.tcNregs
      Co1Three.tcProg Co1Three.tcSpec = true) ∧
    (cpCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2 Co1Three.cpNregs
      Co1Three.cpProg Co1Three.cpSpec = true) ∧ (Co1Three.cpSpec.noFun = true) :=
  ⟨tc_of (by norm_num) c1A c1B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co1ttc_K,
    cp_of (by norm_num) c1A c1B (by decide +kernel) (by decide +kernel) (by decide +kernel)
      co1tcp_K,
    by decide +kernel⟩

end CertificateChecks.KernelTc

end
