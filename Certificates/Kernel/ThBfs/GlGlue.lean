module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.OrbitData
public import Certificates.Kernel.ThBfs.GlChk
public import CFSG.Certificates.Kernel.ThBfs.Sound
import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.ThBfs.GlFacts

public section

namespace CertificateChecks.KernelThBfs

open CFSG.KC.Misc.Clos CFSG.KC.ThBfs CFSG.EvenSporadicStandard.ThStd.LocalDataTh

noncomputable def decGl (e : ℕ) : List ℕ := [e % 16, e / 16 % 16, e / 256 % 16, e / 4096 % 16]

theorem decGl_inj {a b : ℕ} (ha : a < 65536) (hb : b < 65536) (h : decGl a = decGl b) : a = b := by
  simp only [decGl, List.cons.injEq, and_true] at h
  omega

theorem glImg_T1c : ∀ c < 16, glImg 0 c = applyCols 4 T1c c := by decide +kernel

theorem glImg_T2c : ∀ c < 16, glImg 1 c = applyCols 4 T2c c := by decide +kernel

theorem glImg_lt (k c : ℕ) : glImg k c < 16 := Nat.mod_lt _ (by norm_num)

theorem decGl_glAct' {k : ℕ} {T : List ℕ} (hT : ∀ c < 16, glImg k c = applyCols 4 T c) (e : ℕ) :
    decGl (glAct e k) = mulCols 4 T (decGl e) := by
  have hm : mulCols 4 T (decGl e) = [applyCols 4 T (e % 16), applyCols 4 T (e / 16 % 16),
      applyCols 4 T (e / 256 % 16), applyCols 4 T (e / 4096 % 16)] := rfl
  have hact : glAct e k = glImg k (e % 16) + (16 * glImg k (e / 16 % 16) +
      (256 * glImg k (e / 256 % 16) + 4096 * glImg k (e / 4096 % 16))) := rfl
  rw [hm, hact, ← hT (e % 16) (Nat.mod_lt _ (by norm_num)),
    ← hT (e / 16 % 16) (Nat.mod_lt _ (by norm_num)), ← hT (e / 256 % 16) (Nat.mod_lt _ (by norm_num)),
    ← hT (e / 4096 % 16) (Nat.mod_lt _ (by norm_num))]
  have ha := glImg_lt k (e % 16)
  have hb := glImg_lt k (e / 16 % 16)
  have hc := glImg_lt k (e / 256 % 16)
  have hd := glImg_lt k (e / 4096 % 16)
  generalize glImg k (e % 16) = a at ha ⊢
  generalize glImg k (e / 16 % 16) = b at hb ⊢
  generalize glImg k (e / 256 % 16) = c at hc ⊢
  generalize glImg k (e / 4096 % 16) = d at hd ⊢
  simp only [decGl, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem decGl_glAct (e k : ℕ) (hk : k < [mulCols 4 T1c, mulCols 4 T2c].length) :
    decGl (glAct e k) = [mulCols 4 T1c, mulCols 4 T2c][k] (decGl e) := by
  rcases k with _ | _ | k
  · exact decGl_glAct' glImg_T1c e
  · exact decGl_glAct' glImg_T2c e
  · simp at hk

theorem glAt_all :
    ∀ i < 20160, bfsAt glAct 65536 [mulCols 4 T1c, mulCols 4 T2c].length 20160 GR GC GS i = true :=
  forall_of_chunks 1260 16 glAt fun c hc => by
    interval_cases c
    exacts [ch24203_r0, ch24203_r1, ch24203_r2, ch24203_r3, ch24203_r4, ch24203_r5, ch24203_r6,
      ch24203_r7, ch24203_r8, ch24203_r9, ch24203_r10, ch24203_r11, ch24203_r12, ch24203_r13,
      ch24203_r14, ch24203_r15]

theorem glList_length : glList.length = 20160 := by
  have h0 : decGl (keyAt GR 0) = idCols 4 := by
    rw [ch24203_root]
    rfl
  rw [glList, bfsAt_sound [mulCols 4 T1c, mulCols 4 T2c] decGl (fun e _ k hk => decGl_glAct e k hk)
    (fun a ha b hb h => decGl_inj ha hb h) (by norm_num) glAt_all h0 (by norm_num)]
  simp

theorem glFacts : GLFacts = true := glFacts_of_length glList_length

end CertificateChecks.KernelThBfs

end
