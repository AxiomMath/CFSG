module

public import Certificates.Kernel.Sporadic.Fi22.Or9555W0
public import Certificates.Kernel.Sporadic.Fi22.Or9555W1
public import Certificates.Kernel.Sporadic.Fi22.Or9555W2
public import Certificates.Kernel.Sporadic.Fi22.Or9555W3
public import Certificates.Kernel.Sporadic.Fi22.Or9555W4
public import Certificates.Kernel.Sporadic.Fi22.Or9555S
public import CFSG.Certificates.Kernel.SetWalkSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Or9555

open CFSG.KC.Enum CFSG.KC.SetWalk CertificateChecks.KernelSpor

theorem chunks : ∀ c < 45, or9555ck c = true := by
  intro c hc
  interval_cases c
  exacts [or9555ck0, or9555ck1, or9555ck2, or9555ck3, or9555ck4, or9555ck5, or9555ck6, or9555ck7,
    or9555ck8, or9555ck9, or9555ck10, or9555ck11, or9555ck12, or9555ck13, or9555ck14, or9555ck15,
    or9555ck16, or9555ck17, or9555ck18, or9555ck19, or9555ck20, or9555ck21, or9555ck22, or9555ck23,
    or9555ck24, or9555ck25, or9555ck26, or9555ck27, or9555ck28, or9555ck29, or9555ck30, or9555ck31,
    or9555ck32, or9555ck33, or9555ck34, or9555ck35, or9555ck36, or9555ck37, or9555ck38, or9555ck39,
    or9555ck40, or9555ck41, or9555ck42, or9555ck43, or9555ck44]

theorem sorts : ∀ j < 16, or9555sk j = true := by
  intro j hj
  interval_cases j
  exacts [or9555sk0, or9555sk1, or9555sk2, or9555sk3, or9555sk4, or9555sk5, or9555sk6, or9555sk7,
    or9555sk8, or9555sk9, or9555sk10, or9555sk11, or9555sk12, or9555sk13, or9555sk14, or9555sk15]

theorem roots : listK 12 4095 CFSG.AGLEmbedding.KFactProofs.Fi22Five.s0List (Or9555C 0) = true ∧
    Or9555C 1 = pcomp 360 12 4095 (Fi22W.G 0) (Or9555C 0) ∧
    Or9555C 2 = pcomp 360 12 4095 (Fi22W.G 1) (Or9555C 0) ∧
    Or9555C 3 = pcomp 360 12 4095 (Fi22W.G 1) (pcomp 360 12 4095 (Fi22W.G 0) (Or9555C 0)) ∧
    Or9555P 0 = 0 + 1 * 1048576 ∧ Or9555P 1 = 1 + 1576 * 1048576 ∧
    Or9555P 2 = 1576 + 23976 * 1048576 ∧ Or9555P 3 = 23976 + 61776 * 1048576 ∧
    fixOK 360 12 4095 (Fi22Pin.pin 6) (Or9555C 0) = true ∧
    fixOK 360 12 4095 (Fi22Pin.pin 7) (Or9555C 0) = true := by
  have h := root
  unfold rootOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem keys_inj : ∀ a < 61776, ∀ b < 61776, keyR Or9555T a = keyR Or9555T b → a = b := by
  refine inj_of_sorted (SKT := Or9555K) fun j hj => ?_
  have hb : j / 4096 < 16 := by omega
  have hs := sortOK_spec (sorts _ hb)
  have e : j = j / 4096 * 4096 + j % 4096 := by omega
  have ht : j % 4096 < len (j / 4096) := by
    by_cases h15 : j / 4096 < 15
    · have : len (j / 4096) = 4096 := by
        simp only [len]
        rw [show Nat.blt (j / 4096) 15 = true from Nat.blt_eq.mpr h15]
      rw [this]
      exact Nat.mod_lt _ (by norm_num)
    · have h' : j / 4096 = 15 := by omega
      have : len (j / 4096) = 335 := by
        rw [h']
        rfl
      rw [this]
      omega
  have := hs (j % 4096) ht
  have e' : Nat.mul (j / 4096) 4096 + j % 4096 = j := by
    rw [Nat.mul_eq]
    omega
  rw [e'] at this
  exact this

end CertificateChecks.KernelSpor.Or9555

end
