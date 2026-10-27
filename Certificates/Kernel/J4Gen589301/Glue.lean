module

public import Certificates.Kernel.J4Gen589301.Checks
public import Certificates.Kernel.J4NPVerdict.Glue
public import CFSG.Certificates.Kernel.J4Gen589301.Sound

public section

namespace CertificateChecks.KernelJ4Gen

open CFSG.Sporadic.J4 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.KC.J4NPV CFSG.KC.J4Gen
  CertificateChecks.KernelJ4Q CertificateChecks.KernelJ4NPV CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.J4 CFSG.Quasithin.KGC31.J4M4 CFSG.Quasithin.KGC31.J4M4.Gen

theorem slpZ_eq : slpZ = parseL CFSG.KD.J4Gen.LZ := by
  rw [CFSG.KD.J4Gen.LZ_eq, parseSlp_ofList]

theorem slpC_eq : slpC = parseL CFSG.KD.J4Gen.LC := by
  rw [CFSG.KD.J4Gen.LC_eq, parseSlp_ofList]

theorem slpAB_eq : slpAB = parseL CFSG.KD.J4Gen.LAB := by
  rw [CFSG.KD.J4Gen.LAB_eq, parseSlp_ofList]

theorem inp3 {M₀ M₁ M₂ : Nat} {f : ℕ → J} (h₀ : VjRep M₀ (f 0)) (h₁ : VjRep M₁ (f 1))
    (h₂ : VjRep M₂ (f 2)) (h₃ : ∀ k, 3 ≤ k → f k = 1) : ∀ k, VjRep (getN one [M₀, M₁, M₂] k) (f k)
  | 0 => h₀
  | 1 => h₁
  | 2 => h₂
  | k + 3 => by
    rw [h₃ (k + 3) (by omega)]
    exact vjRep_one hK

theorem m4gen_ge {k : ℕ} (hk : 2 ≤ k) : m4gen k = 1 := by
  unfold m4gen
  rw [if_neg (by omega), if_neg (by omega)]

theorem baseJ_ge {k : ℕ} (hk : 2 ≤ k) : baseJ k = 1 := by
  unfold baseJ
  rw [if_neg (by omega), if_neg (by omega)]

theorem hW : ∀ k, VjRep (getN one [W1, W2] k) (m4gen k) := fun k => (vjg_w k).1

theorem hA : VjRep A a := by
  have h := vjg_base 0
  have e : baseJ 0 = a := if_pos rfl
  rw [e] at h
  exact h

theorem hB : VjRep B b := by
  have h := vjg_base 1
  have e : baseJ 1 = b := by
    unfold baseJ
    rw [if_neg (by omega), if_pos rfl]
  rw [e] at h
  exact h

theorem hZ : VjRep CFSG.KD.J4Gen.Z z1Elt := by
  have h := runK_out hK hW ch589301Z
  rw [← slpZ_eq, ← z1Elt_def] at h
  exact h

theorem hC : VjRep CFSG.KD.J4Gen.C cElt := by
  have hin : ∀ k, VjRep (getN one [A, B, CFSG.KD.J4Gen.Z] k) (inpC k) := by
    refine inp3 ?_ ?_ ?_ ?_
    · rw [inpC, if_neg (by omega)]
      exact vjg_base 0
    · rw [inpC, if_neg (by omega)]
      exact vjg_base 1
    · rw [inpC, if_pos rfl]
      exact hZ
    · intro k hk
      rw [inpC, if_neg (by omega), baseJ_ge (by omega)]
  have h := runK_out hK hin ch589301C
  rw [← slpC_eq, ← cElt_def] at h
  exact h

theorem hAPBP : VjRep CFSG.KD.J4Gen.AP apElt ∧ VjRep CFSG.KD.J4Gen.BP bpElt := by
  have hin : ∀ k, VjRep (getN one [W1, W2, CFSG.KD.J4Gen.C] k) (inpAB k) := by
    refine inp3 ?_ ?_ ?_ ?_
    · rw [inpAB, if_neg (by omega)]
      exact hW 0
    · rw [inpAB, if_neg (by omega)]
      exact hW 1
    · rw [inpAB, if_pos rfl]
      exact hC
    · intro k hk
      rw [inpAB, if_neg (by omega), m4gen_ge (by omega)]
  have h := runK_out2 hK hin ch589301AB
  rw [← slpAB_eq, ← apElt_def, ← bpElt_def] at h
  exact h

theorem hU : VjRep (wordJ c rm one [W1, W2] [W1i, W2i] uWord) uElt := by
  rw [uElt_def]
  exact vjRep_wordJ hK (fun i => (vjg_w i).1) (fun i => (vjg_w i).2) uWord

theorem hF : VjRep FM_9 (fJ 9) := by
  have h := vjg_fm (j := 9) (by omega)
  have e : vjT.fm.getD 9 0 = FM_9 := rfl
  rw [e] at h
  exact h

theorem facts589301 :
    z1Elt * z1Elt = 1 ∧ cElt ^ 11 = 1 ∧ cElt * z1Elt = z1Elt * cElt ∧
      uElt * z1Elt * uElt⁻¹ = fJ 9 ∧
      ∃ gM : GL (Fin 112) (ZMod 2),
        ((apElt : G₀) : GL (Fin 112) (ZMod 2)) * gM = gM * gA ∧
          ((bpElt : G₀) : GL (Fin 112) (ZMod 2)) * gM = gM * gB := by
  obtain ⟨hap, hbp⟩ := hAPBP
  rw [← a_coe, ← b_coe]
  exact factsK_sound hK hZ hC hU hF hap hbp hA hB ch589301F

end CertificateChecks.KernelJ4Gen

end
