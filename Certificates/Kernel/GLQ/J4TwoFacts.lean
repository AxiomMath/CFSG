module

public import Certificates.Kernel.GLQ.J4Two

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.J4Two

open CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.J4TwoRank CFSG.KC.OpsK
open CFSG.KC.OpsHom CertificateChecks.KernelLC.J4R CFSG.KC.Co1F2

theorem decA : (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed1 = unpackR 112 JA.M := by
  change CFSG.Sporadic.SmallF2.Native.rowsOfPayload 112 CFSG.Blueprint.NativeSporadic.J4Seed1 = _
  rw [JA.eq]
  exact bind_sound JA.bind

theorem decB : (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed2 = unpackR 112 JB.M := by
  change CFSG.Sporadic.SmallF2.Native.rowsOfPayload 112 CFSG.Blueprint.NativeSporadic.J4Seed2 = _
  rw [JB.eq]
  exact bind_sound JB.bind

theorem outs_lt : ∀ i : Fin 11, j4Outs i < 50 := by decide +kernel

theorem j4_gen {V' : Type} {O' : Ops Nat V'} (H : Hom (ops2 112) O') {A B : Nat}
    (hPA : H.P A) (hPB : H.P B)
    (hA : (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed1 = H.U A)
    (hB : (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed2 = H.U B)
    (hk : elem2OK O' (List.ofFn fun i =>
      (runProgN O' (initRegsN O' 50 (A, A) (B, O'.pow B 3)) j4Prog)[j4Outs i]!.1) [0] = true) :
    j4Check = true := by
  obtain ⟨hB3, hPB3⟩ := H.pow_U 3 hPB
  have hinit : initRegsN (ops2 112) 50 ((ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed1,
      (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed1)
      ((ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed2,
        (ops2 112).pow ((ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed2) 3) =
      (initRegsN O' 50 (A, A) (B, O'.pow B 3)).map H.UU := by
    rw [hA, hB, hB3]
    exact H.initRegsN_U 50 (A, A) (B, O'.pow B 3)
  obtain ⟨hrun, hsize, hP⟩ := H.runProgN_U 50 j4Prog kLt (initRegsN O' 50 (A, A) (B, O'.pow B 3))
    (by simp [initRegsN]) (H.initRegsN_P ⟨hPA, hPA⟩ ⟨hPB, hPB3⟩)
  unfold j4Check
  rw [kLt, Bool.true_and]
  unfold j4Regs
  rw [hinit, hrun]
  generalize runProgN O' (initRegsN O' 50 (A, A) (B, O'.pow B 3)) j4Prog = R at hsize hP hk ⊢
  have hl : (List.ofFn fun i => (R.map H.UU)[j4Outs i]!.1) =
      (List.ofFn fun i => R[j4Outs i]!.1).map H.U := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    rw [get_map _ H.UU (by rw [hsize]; exact outs_lt i)]
    rfl
  rw [hl, H.elem2OK_U ?_ [0]]
  · exact hk
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact (hP _ (by rw [hsize]; exact outs_lt i)).1

theorem j4_of {A B : Nat}
    (hA : (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed1 = unpackR 112 A)
    (hB : (ops2 112).decode CFSG.Blueprint.NativeSporadic.J4Seed2 = unpackR 112 B)
    (hk : forceB (powN (opsF2K 112) 4 B 3) (fun B3 => runK (opsF2K 112) j4Prog
      (initRegsN (opsF2K 112) 50 (A, A) (B, B3)) outsK) = true) : j4Check = true := by
  rw [forceB_eq, powN_eq _ _ _ _ (by norm_num), runK_eq] at hk
  unfold outsK at hk
  rw [forceL_eq] at hk
  exact j4_gen (hom2 112 (by norm_num)) trivial trivial hA hB hk

theorem j4_ok : j4Check = true := j4_of decA decB kJ4

end CertificateChecks.KernelGLQ.J4Two

end
