module

public import Certificates.Kernel.FrameWhole.Checks
public import Certificates.Kernel.FrameE78.Glue
public import CFSG.Certificates.Kernel.FrameWhole.Glue
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KD.FrameWhole

open CFSG.KC.Enum CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl CFSG.KC.FrameWhole CFSG.KD.FrameE78

private theorem sym6 : ∀ i < 6, ∀ j < 6, cij C6 j i = cij C6 i j := by decide +kernel

theorem cm6_symm : (Cm 6 C6).IsSymm :=
  Matrix.IsSymm.ext fun i j => congrArg (fun z : ℕ => (z : ZMod 3)) (sym6 i i.isLt j j.isLt)

@[expose] def WholeFacts (n C m d : ℕ) : Prop :=
  {r | ConjDer (sS (Cm n C)) r}.ncard = m ∧
    (∀ r, ConjDer (sS (Cm n C)) r →
      {t | ConjDer (sS (Cm n C)) t ∧ r * t ≠ t * r}.ncard = d) ∧
    ∀ r t, ConjDer (sS (Cm n C)) r → ConjDer (sS (Cm n C)) t →
      Relation.ReflTransGen (fun a b => ConjDer (sS (Cm n C)) a ∧ ConjDer (sS (Cm n C)) b ∧
        a * b ≠ b * a) r t

theorem whole6_facts : WholeFacts 6 C6 36 20 := by
  have h := ch709590r6
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact whole_facts (LV := LV6) (by decide) (by decide) cm6_symm h1 h2 h3 h4 h5 ch709590u6
    ch709590k6

theorem whole7_facts : WholeFacts 7 C7 63 32 := by
  have h := ch709548r7
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact whole_facts (LV := LV7) (by decide) (by decide) cm7_symm h1 h2 h3 h4 h5 ch709590u7
    ch709590k7

theorem whole8_facts : WholeFacts 8 C8 120 56 := by
  have h := ch709548r8
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact whole_facts (LV := LV8) (by decide) (by decide) cm8_symm h1 h2 h3 h4 h5 ch709590u8
    ch709590k8

end CFSG.KD.FrameWhole

end
